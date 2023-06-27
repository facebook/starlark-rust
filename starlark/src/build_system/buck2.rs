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
    pub(crate) fn new(workspace_dir: Option<&PathBuf>) -> Option<Self> {
        // We always need the workspace dir to resolve the workspace name.
        let workspace_dir = workspace_dir?;

        let mut raw_command = Command::new("buck2");
        let command = raw_command
            .arg("audit")
            .arg("cell")
            .arg("--json")
            .current_dir(workspace_dir);

        let output = command.output().ok()?;
        if !output.status.success() {
            return None;
        }

        let repositories =
            serde_json::from_slice::<HashMap<String, PathBuf>>(&output.stdout).ok()?;
        let workspace_name = repositories.iter().find_map(|(name, path)| {
            if path == workspace_dir {
                Some(name.clone())
            } else {
                None
            }
        })?;

        Some(Self {
            workspace_name,
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
                path.strip_prefix(repository_path)
                    .ok()
                    .map(|stripped_path| (Cow::Borrowed(name.as_str()), stripped_path))
            })
    }

    fn should_use_at_sign_before_repository_name(&self) -> bool {
        false
    }
}
