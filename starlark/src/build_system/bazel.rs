use std::borrow::Cow;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use crate::build_system::BuildSystem;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BazelBuildSystem {
    workspace_name: Option<String>,
    output_base: PathBuf,
}

impl BazelBuildSystem {
    const DEFAULT_WORKSPACE_NAME: &'static str = "__main__";

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
                output_base: PathBuf::from(output_base),
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
        let mut path = self.output_base.join("external");
        path.push(repository_name);
        Some(Cow::Owned(path))
    }
}
