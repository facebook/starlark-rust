use std::path::PathBuf;

use crate::bazel_info::BazelInfo;

#[derive(PartialEq, Debug)]
pub struct ExternalLabel {
    repository: String,
    package: String,
    target: String,
}

#[derive(PartialEq, Debug)]
pub struct LocalLabel {
    package: String,
    target: String,
}

#[derive(PartialEq, Debug)]
pub struct RelativeLabel {
    sub_package: String,
    target: String,
}

#[derive(PartialEq, Debug)]
pub enum Label {
    External(ExternalLabel),
    Local(LocalLabel),
    Relative(RelativeLabel),
}

impl Label {
    fn split_package_target(label: &str) -> Option<(&str, &str)> {
        let mut split_parts = label.split(":");
        let package = split_parts.next();
        let target = split_parts.next();
        // Support //foo short for //foo:foo
        match (package, target) {
            // to avoid // being a valid label
            // but //:baz being a valid target
            (Some(""), None) => None,
            (Some(package), Some(target)) => Some((package, target)),
            (Some(package), None) => Some((package, package)),
            _ => None,
        }
    }

    fn split_repository_package_target(label: &str) -> Option<(&str, &str, &str)> {
        let mut split_parts = label.split("//");
        let repository = split_parts.next()?;
        match split_parts.next() {
            // empty package-target could be caused by @foo//  or // which we don't want to support so return None
            Some("") => None,
            Some(package_target) => {
                let (package, target) = Self::split_package_target(package_target)?;
                Some((repository, package, target))
            }
            // @foo shorthand for @foo//:foo
            None => Some((repository, "", repository)),
        }
    }

    pub fn replace_fake_file_with_build_target(fake_file: PathBuf) -> Option<PathBuf> {
        if fake_file.exists() {
            return Some(fake_file);
        }
        fake_file.parent().and_then(|p| {
            let build = p.join("BUILD");
            let build_bazel = p.join("BUILD.bazel");
            if build_bazel.exists() {
                Some(build_bazel)
            } else if build.exists() {
                Some(build)
            } else {
                None
            }
        })
    }

    fn is_file_root_of_workspace(file: PathBuf) -> bool {
        match file.file_name().and_then(|name| name.to_str()) {
            Some(name) => name.starts_with("WORKSPACE") || name == "MODULE.bazel",
            _ => false,
        }
    }

    fn resolve_local(
        bazel_info: &BazelInfo,
        current_file_dir: PathBuf,
        l: LocalLabel,
    ) -> Option<PathBuf> {
        for a in current_file_dir.ancestors() {
            for file in a.read_dir().ok()? {
                match file {
                    Ok(file) => {
                        if Self::is_file_root_of_workspace(file.path()) {
                            return Some(a.to_path_buf().join(l.package).join(l.target));
                        }
                    }
                    _ => {}
                }
            }
        }
        Some(bazel_info.workspace_root.join(l.package).join(l.target))
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
                    let external_directory = bazel_info.output_base.join("external");
                    let repositories: Vec<String> = external_directory
                        .read_dir()
                        .ok()?
                        .filter_map(|e| {
                            e.ok()
                                .and_then(|f| Some(f.file_name().to_str().unwrap_or("").to_owned()))
                                .filter(|name| {
                                    let repository_with_version = l.repository.clone() + ".";
                                    name == l.repository.as_str()
                                        || name.starts_with(repository_with_version.as_str())
                                })
                        })
                        .collect();

                    match repositories.len() {
                        1 => repositories.get(0).and_then(|repo| {
                            Some(external_directory.join(repo).join(l.package).join(l.target))
                        }),
                        _ => None,
                    }
                }
            }
            Label::Local(l) => {
                current_file_dir.and_then(|dir| Self::resolve_local(bazel_info, dir, l))
            }

            Label::Relative(l) => {
                current_file_dir.and_then(|d| Some(d.join(l.sub_package).join(l.target)))
            }
        }
    }

    pub fn new(label: &str) -> Option<Self> {
        // to avoid the "" label being valid
        if label.len() == 0 {
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

        if label.contains(":") {
            let (package, target) = Self::split_package_target(label)?;
            Some(Label::Relative(RelativeLabel {
                sub_package: package.to_owned(),
                target: target.to_owned(),
            }))
        } else {
            // To support foo being shorthand for :foo
            Some(Label::Relative(RelativeLabel {
                sub_package: "".into(),
                target: label.to_owned(),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ExternalLabel;
    use super::Label;
    use super::LocalLabel;
    use super::RelativeLabel;

    fn external_label(repository: &str, package: &str, target: &str) -> Label {
        Label::External(ExternalLabel {
            repository: repository.to_owned(),
            package: package.to_owned(),
            target: target.to_owned(),
        })
    }

    fn local_label(package: &str, target: &str) -> Label {
        Label::Local(LocalLabel {
            package: package.to_owned(),
            target: target.to_owned(),
        })
    }
    fn relative_label(package: &str, target: &str) -> Label {
        Label::Relative(RelativeLabel {
            sub_package: package.to_owned(),
            target: target.to_owned(),
        })
    }

    #[test]
    fn external() {
        assert_eq!(
            Label::new("@foo//bar:baz"),
            Some(external_label("foo", "bar", "baz"))
        )
    }

    #[test]
    fn external_no_target() {
        assert_eq!(
            Label::new("@foo//bar"),
            Some(external_label("foo", "bar", "bar"))
        )
    }

    #[test]
    fn external_no_package() {
        assert_eq!(Label::new("@foo"), Some(external_label("foo", "", "foo")))
    }

    #[test]
    fn external_empty_package_with_target() {
        assert_eq!(
            Label::new("@foo//:baz"),
            Some(external_label("foo", "", "baz"))
        )
    }

    #[test]
    fn external_empty_package_invalid() {
        assert_eq!(Label::new("@foo//"), None)
    }

    #[test]
    fn local() {
        assert_eq!(Label::new("//bar:baz"), Some(local_label("bar", "baz")))
    }

    #[test]
    fn local_no_target() {
        assert_eq!(Label::new("//bar"), Some(local_label("bar", "bar")))
    }

    #[test]
    fn local_no_package() {
        assert_eq!(Label::new("//:baz"), Some(local_label("", "baz")))
    }

    #[test]
    fn local_no_package_invalid() {
        assert_eq!(Label::new("//"), None)
    }

    #[test]
    fn relative() {
        assert_eq!(Label::new("bar:baz"), Some(relative_label("bar", "baz")))
    }

    #[test]
    fn relative_no_target() {
        assert_eq!(Label::new("baz"), Some(relative_label("", "baz")))
    }

    #[test]
    fn relative_only_target() {
        assert_eq!(Label::new(":baz"), Some(relative_label("", "baz")))
    }

    #[test]
    fn empty() {
        assert_eq!(Label::new(""), None)
    }
}
