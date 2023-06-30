use std::borrow::Cow;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use crate::build_system::BuildSystem;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BazelBuildSystem {
    workspace_name: Option<String>,
    external_output_base: PathBuf,
}

impl BazelBuildSystem {
    const DEFAULT_WORKSPACE_NAME: &'static str = "__main__";
    const BUILD_FILE_NAMES: [&'static str; 2] = ["BUILD", "BUILD.bazel"];
    const LOADABLE_EXTENSIONS: [&'static str; 1] = ["bzl"];

    pub(crate) fn new(workspace_dir: Option<&PathBuf>) -> Option<Self> {
        let mut raw_command = Command::new("bazel");
        let mut command = raw_command.arg("info");
        if let Some(workspace_dir) = workspace_dir {
            command = command.current_dir(workspace_dir);
        }

        let output = command.output().ok()?;
        if !output.status.success() {
            return None;
        }

        let output = String::from_utf8(output.stdout).ok()?;
        let mut execroot = None;
        let mut output_base = None;
        for line in output.lines() {
            if let Some((key, value)) = line.split_once(": ") {
                match key {
                    "execution_root" => execroot = Some(value),
                    "output_base" => output_base = Some(value),
                    _ => {}
                }
            }
        }

        if let (Some(execroot), Some(output_base)) = (execroot, output_base) {
            Some(Self {
                workspace_name: match PathBuf::from(execroot)
                    .file_name()?
                    .to_string_lossy()
                    .to_string()
                {
                    name if name == Self::DEFAULT_WORKSPACE_NAME => None,
                    name => Some(name),
                },
                external_output_base: PathBuf::from(output_base).join("external"),
            })
        } else {
            None
        }
    }
}

impl BuildSystem for BazelBuildSystem {
    fn root_repository_name(&self) -> Option<&str> {
        self.workspace_name.as_deref()
    }

    fn repository_path(&self, repository_name: &str) -> Option<Cow<Path>> {
        let path = self.external_output_base.join(repository_name);
        Some(Cow::Owned(path))
    }

    fn repository_for_path<'a>(&'a self, path: &'a Path) -> Option<(Cow<'a, str>, &'a Path)> {
        if let Ok(path) = path.strip_prefix(&self.external_output_base) {
            let mut path_components = path.components();

            let repository_name = path_components.next()?.as_os_str().to_string_lossy();
            let repository_path = path_components.as_path();

            Some((repository_name, repository_path))
        } else {
            None
        }
    }

    fn repository_names(&self) -> Vec<Cow<str>> {
        let mut names = Vec::new();
        if let Some(workspace_name) = &self.workspace_name {
            names.push(Cow::Borrowed(workspace_name.as_str()));
        }

        // Look for existing folders in `external_output_base`.
        if let Ok(entries) = std::fs::read_dir(&self.external_output_base) {
            for entry in entries {
                if let Ok(entry) = entry {
                    if let Ok(file_type) = entry.file_type() {
                        if file_type.is_dir() {
                            if let Some(name) = entry.file_name().to_str() {
                                names.push(Cow::Owned(name.to_string()));
                            }
                        }
                    }
                }
            }
        }
        names
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
        let mut raw_command = Command::new("bazel");
        let mut command = raw_command.arg("query").arg(format!("{module}*"));
        if let Some(workspace_dir) = workspace_dir {
            command = command.current_dir(workspace_dir);
        }

        let output = command.output().ok()?;
        if !output.status.success() {
            return None;
        }

        let output = String::from_utf8(output.stdout).ok()?;
        Some(
            output
                .lines()
                .filter_map(|line| line.strip_prefix(module).map(|str| str.to_owned()))
                .collect(),
        )
    }
}
