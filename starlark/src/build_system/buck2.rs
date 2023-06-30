use std::borrow::Cow;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use crate::build_system::BuildSystem;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Buck2BuildSystem {
    workspace_name: String,
    repositories: HashMap<String, PathBuf>,
}

impl Buck2BuildSystem {
    const BUILD_FILE_NAMES: [&'static str; 1] = ["BUCK"];
    const LOADABLE_EXTENSIONS: [&'static str; 1] = ["bzl"];

    pub(crate) fn new(workspace_dir: Option<&PathBuf>) -> Option<Self> {
        // We always need the workspace dir to resolve the workspace name.
        let workspace_dir = workspace_dir?;

        let mut raw_command = Command::new("buck2");
        let command = raw_command
            .arg("audit")
            .arg("cell")
            .arg("--aliases")
            .arg("--json")
            .current_dir(workspace_dir);

        let output = command.output().ok()?;
        if !output.status.success() {
            return None;
        }

        let mut workspace_name = None;
        let repositories = serde_json::from_slice::<HashMap<String, PathBuf>>(&output.stdout)
            .ok()?
            .into_iter()
            .filter_map(|(name, path)| {
                if &path == workspace_dir {
                    workspace_name = Some(name);
                    None
                } else {
                    Some((name, path))
                }
            })
            .collect();

        Some(Self {
            workspace_name: workspace_name?,
            repositories,
        })
    }
}

impl BuildSystem for Buck2BuildSystem {
    fn root_repository_name(&self) -> Option<&str> {
        Some(&self.workspace_name)
    }

    fn repository_path(&self, repository_name: &str) -> Option<Cow<Path>> {
        self.repositories
            .get(repository_name)
            .map(|path| Cow::Borrowed(path.as_path()))
    }

    fn repository_for_path<'a>(&'a self, path: &'a Path) -> Option<(Cow<'a, str>, &'a Path)> {
        self.repositories
            .iter()
            .find_map(|(name, repository_path)| {
                if path.starts_with(repository_path) {
                    Some((Cow::Borrowed(name.as_str()), repository_path.as_path()))
                } else {
                    None
                }
            })
    }

    fn repository_names(&self) -> Vec<Cow<str>> {
        self.repositories
            .keys()
            .map(|name| name.as_str())
            .map(Cow::Borrowed)
            .collect()
    }

    fn get_build_file_names(&self) -> &[&str] {
        &Self::BUILD_FILE_NAMES
    }

    fn get_loadable_extensions(&self) -> &[&str] {
        &Self::LOADABLE_EXTENSIONS
    }

    fn query_buildable_targets(
        &self,
        module: &str,
        workspace_dir: Option<&Path>,
    ) -> Option<Vec<String>> {
        let mut raw_command = Command::new("buck2");
        let mut command = raw_command
            .arg("uquery")
            // buck2 query doesn't like `@` prefixes.
            .arg(module.trim_start_matches('@'))
            .arg("--json");
        if let Some(workspace_dir) = workspace_dir {
            command = command.current_dir(workspace_dir);
        }

        let output = command.output().ok()?;
        if !output.status.success() {
            return None;
        }

        let output = String::from_utf8(output.stdout).ok()?;
        serde_json::from_str(&output).ok()
    }

    fn should_use_at_sign_before_repository_name(&self) -> bool {
        false
    }
}
