//! Build system support. Allows to resolve the repository structure, including external
//! repositories.

use std::borrow::Cow;
use std::path::Path;
use std::path::PathBuf;

use clap::ValueEnum;

mod bazel;
mod buck2;

/// A hint for which build system to resolve.
#[derive(ValueEnum, Debug, Clone, PartialEq, Eq)]
pub enum BuildSystemHint {
    /// Try to resolve Bazel.
    Bazel,
    /// Try to resolve Buck2.
    Buck2,
}

/// A build system provides information about the repository structure.
pub trait BuildSystem: std::fmt::Debug + Send + Sync {
    /// Returns the name of the root repository.
    fn root_repository_name(&self) -> Option<&str>;

    /// Returns the path of the repository with the given name.
    fn repository_path(&self, repository_name: &str) -> Option<Cow<Path>>;

    /// Given a path, tries to resolve the repository name and the path
    /// relative to the root of repository. Returns `None` if the path is not
    /// part of a known repository.
    fn repository_for_path<'a>(&'a self, path: &'a Path) -> Option<(Cow<'a, str>, &'a Path)>;

    /// Returns the names of all known repositories.
    fn repository_names(&self) -> Vec<Cow<str>>;

    /// Get valid build file names for this build system.
    fn get_build_file_names(&self) -> &[&str];

    /// Get valid file extensions for this build system.
    fn get_loadable_extensions(&self) -> &[&str];

    /// Ask the build system for the build targets that are buildable from the
    /// given module. The `module` parameter should always end with a `:`.
    fn query_buildable_targets(
        &self,
        module: &str,
        workspace_dir: Option<&Path>,
    ) -> Option<Vec<String>>;

    /// Whether to prefix absolute paths with `@` when that path contains a
    /// repository name.
    fn should_use_at_sign_before_repository_name(&self) -> bool {
        true
    }
}

/// Tries to resolve the build system from the current working directory.
/// You can optionally provide a hint to only try a specific build system.
/// If no hint is provided, the build systems are tried in the following order:
/// - Buck2
/// - Bazel
pub fn try_resolve_build_system(
    workspace_dir: Option<&PathBuf>,
    hint: Option<BuildSystemHint>,
) -> Option<Box<dyn BuildSystem>> {
    match hint {
        Some(BuildSystemHint::Bazel) => {
            Some(Box::new(bazel::BazelBuildSystem::new(workspace_dir)?))
        }
        Some(BuildSystemHint::Buck2) => {
            Some(Box::new(buck2::Buck2BuildSystem::new(workspace_dir)?))
        }
        None => {
            if let Some(build_system) =
                try_resolve_build_system(workspace_dir, Some(BuildSystemHint::Buck2))
            {
                Some(build_system)
            } else if let Some(build_system) =
                try_resolve_build_system(workspace_dir, Some(BuildSystemHint::Bazel))
            {
                Some(build_system)
            } else {
                None
            }
        }
    }
}
