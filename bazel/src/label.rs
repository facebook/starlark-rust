
use std::path::PathBuf;

use crate::bazel_info::BazelInfo;

pub struct ExternalLabel {
    repository: String,
    package: String,
    target: String,
}
pub struct LocalLabel {
    package: String,
    target: String,
}

pub struct RelativeLabel {
    sub_package: String,
    target: String,
}

pub enum Label {
    External(ExternalLabel),
    Local(LocalLabel),
    Relative(RelativeLabel),
}

impl Label {
    fn split_package_target(label: &str) -> Option<(&str, &str)> {
        let mut split_parts = label.split(":");
        let package = split_parts.next()?;
        let target = split_parts.next()?;
        Some((package, target))
    }

    fn split_repository_package_target(label: &str) -> Option<(&str, &str, &str)> {
        let mut split_parts = label.split("//");
        let repository = split_parts.next()?;
        let package_target = split_parts.next()?;
        let (package, target) = Self::split_package_target(package_target)?;
        Some((repository, package, target))
    }

    pub fn replace_fake_file_with_build_target(fake_file: PathBuf) -> Option<PathBuf> {
        if fake_file.exists() {
            return Some(fake_file);
        }
        fake_file.parent().and_then(|p| {
            let build = p.join("BUILD");
            let build_bazel = p.join("BUILD.bazel");
            if build.exists() {
                Some(build)
            } else if build_bazel.exists() {
                Some(build_bazel)
            } else {
                None
            }
        })
    }

    pub fn resolve(
        self,
        bazel_info: &BazelInfo,
        current_file_dir: Option<PathBuf>,
    ) -> Option<PathBuf> {
        // TODO: support nested workspaces either by getting info again or at the start getting the info for all the workspaces in the directory
        match self {
            Label::External(l) => {
                let execroot_dirname = bazel_info.execroot.file_name()?;

                if l.repository == execroot_dirname.to_str()? {
                    Some(bazel_info.workspace_root.join(l.package).join(l.target))
                } else {
                    Some(
                        bazel_info
                            .output_base
                            .join("external")
                            .join(l.repository)
                            .join(l.package)
                            .join(l.target),
                    )
                }
            }
            Label::Local(l) => Some(bazel_info.workspace_root.join(l.package).join(l.target)),
            Label::Relative(l) => {
                current_file_dir.and_then(|d| Some(d.join(l.sub_package).join(l.target)))
            }
        }
    }

    pub fn new(label: &str) -> Option<Self> {
        if !label.contains(":") {
            return None;
        }

        if label.starts_with("@") {
            let (repository, package, target) =
                Self::split_repository_package_target(label.trim_start_matches('@'))?;
            return Some(Label::External(ExternalLabel {
                repository: repository.to_owned(),
                package: package.to_owned(),
                target: target.to_owned(),
            }));
        }
        if label.starts_with("//") {
            let (package, target) = Self::split_package_target(label.trim_start_matches("//"))?;
            return Some(Label::Local(LocalLabel {
                package: package.to_owned(),
                target: target.to_owned(),
            }));
        }

        let (package, target) = Self::split_package_target(label)?;
        Some(Label::Relative(RelativeLabel {
            sub_package: package.to_owned(),
            target: target.to_owned(),
        }))
    }
}
