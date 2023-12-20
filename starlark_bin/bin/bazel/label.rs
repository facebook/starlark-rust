//! Module for parsing bazel labels

use std::fmt;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Label {
    // The repository can be omitted, in which case the label is relative to the current repository
    pub repo: Option<LabelRepo>,
    // The package can be omitted, in which case the label is relative to the current package
    pub package: Option<String>,
    pub name: String,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct LabelRepo {
    pub name: String,
    pub is_canonical: bool,
}

#[derive(thiserror::Error, Debug)]
#[error("Unable to parse the label `{}`", .label)]
pub struct LabelParseError {
    label: String,
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(repo) = &self.repo {
            fmt::Display::fmt(&repo, f)?;
        }

        if let Some(package) = &self.package {
            f.write_str("//")?;
            f.write_str(&package)?;
        }

        f.write_str(":")?;
        f.write_str(&self.name)?;

        Ok(())
    }
}

impl fmt::Display for LabelRepo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(if self.is_canonical { "@@" } else { "@" })?;
        f.write_str(&self.name)?;

        Ok(())
    }
}

impl Label {
    pub fn parse(label: &str) -> Result<Self, LabelParseError> {
        match label.split_once("//") {
            Some((repo_part, rest)) => {
                let repo = if repo_part == "" {
                    None
                } else {
                    Some(Self::parse_repo(repo_part).ok_or_else(|| LabelParseError {
                        label: label.to_string(),
                    })?)
                };

                let (package, name) = rest.split_once(":").unwrap_or_else(|| {
                    // Here the name is implicit, and comes from the last component of the package name
                    if let Some((index, _)) = rest.rmatch_indices('/').last() {
                        (rest, &rest[index + 1..])
                    } else {
                        (rest, rest)
                    }
                });

                Ok(Label {
                    name: name.to_string(),
                    package: Some(package.to_string()),
                    repo,
                })
            }
            // Either we have a repo only (@foo or @@foo), or just a name (foo or :foo)
            None => {
                if let Some(repo) = Self::parse_repo(label) {
                    Ok(Label {
                        name: repo.name.to_string(),
                        repo: Some(repo),
                        package: Some("".to_string()),
                    })
                } else {
                    let name = label.strip_prefix(":").unwrap_or(label);

                    Ok(Label {
                        repo: None,
                        name: name.to_string(),
                        package: None,
                    })
                }
            }
        }
    }

    fn parse_repo(repo: &str) -> Option<LabelRepo> {
        if let Some(repo_name) = repo.strip_prefix("@@") {
            Some(LabelRepo {
                name: repo_name.to_string(),
                is_canonical: true,
            })
        } else if let Some(repo_name) = repo.strip_prefix("@") {
            Some(LabelRepo {
                name: repo_name.to_string(),
                is_canonical: false,
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Label;
    use crate::bazel::label::LabelRepo;

    #[test]
    fn test_parsing_repo_only_labels() {
        assert_eq!(
            Label::parse("@foo").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    is_canonical: false,
                    name: "foo".to_string(),
                }),
                package: Some("".to_string()),
                name: "foo".to_string(),
            }
        );

        assert_eq!(
            Label::parse("@@foo").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    is_canonical: true,
                    name: "foo".to_string(),
                }),
                package: Some("".to_string()),
                name: "foo".to_string(),
            }
        );
    }

    #[test]
    fn test_parsing_name_only_labels() {
        assert_eq!(
            Label::parse("foo").unwrap(),
            Label {
                repo: None,
                package: None,
                name: "foo".to_string(),
            }
        );

        assert_eq!(
            Label::parse(":foo").unwrap(),
            Label {
                repo: None,
                package: None,
                name: "foo".to_string(),
            }
        );
    }

    #[test]
    fn test_full_labels() {
        assert_eq!(
            Label::parse("//foo/bar:baz").unwrap(),
            Label {
                repo: None,
                package: Some("foo/bar".to_string()),
                name: "baz".to_string(),
            }
        );

        assert_eq!(
            Label::parse("@foo//foo/bar:baz").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    name: "foo".to_string(),
                    is_canonical: false
                }),
                package: Some("foo/bar".to_string()),
                name: "baz".to_string(),
            }
        );

        assert_eq!(
            Label::parse("@@foo//foo/bar:baz").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    name: "foo".to_string(),
                    is_canonical: true
                }),
                package: Some("foo/bar".to_string()),
                name: "baz".to_string(),
            }
        );
    }

    #[test]
    fn test_labels_with_implicit_name() {
        assert_eq!(
            Label::parse("@foo//bar/baz").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    name: "foo".to_string(),
                    is_canonical: false
                }),
                package: Some("bar/baz".to_string()),
                name: "baz".to_string(),
            }
        );

        assert_eq!(
            Label::parse("@foo//bar").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    name: "foo".to_string(),
                    is_canonical: false
                }),
                package: Some("bar".to_string()),
                name: "bar".to_string(),
            }
        );

        assert_eq!(
            Label::parse("@@foo//bar").unwrap(),
            Label {
                repo: Some(LabelRepo {
                    name: "foo".to_string(),
                    is_canonical: true
                }),
                package: Some("bar".to_string()),
                name: "bar".to_string(),
            }
        );
    }

    #[test]
    fn test_invalid_labels() {
        assert!(Label::parse("foo//bar/baz").is_err());
    }

    #[test]
    fn test_displaying_labels() {
        assert_eq!(format!("{}", Label::parse(":foo.bzl").unwrap()), ":foo.bzl");
        assert_eq!(
            format!("{}", Label::parse("@foo//bar/baz:qux").unwrap()),
            "@foo//bar/baz:qux"
        );
        assert_eq!(
            format!("{}", Label::parse("//foo/bar").unwrap()),
            "//foo/bar:bar"
        );
    }
}
