use std::fmt::Debug;
use std::path::PathBuf;
use std::process::Command;

#[derive(Debug, Clone, PartialEq)]
pub struct BazelInfo {
    pub workspace_root: PathBuf,
    pub output_base: PathBuf,
    pub execroot: PathBuf,
}

fn parse_bazel_info(info: &str) -> Option<BazelInfo> {
    let mut workspace_root: Option<PathBuf> = None;
    let mut output_base: Option<PathBuf> = None;
    let mut execroot: Option<PathBuf> = None;
    info.split('\n').for_each(|l| {
        let split: Vec<&str> = l.splitn(2, ':').collect();
        if split.len() != 2 {
            return;
        }
        let first = split.get(0);
        let next = split.get(1);
        match (first, next) {
            (Some(key), Some(value)) => match key {
                &"execution_root" => execroot = Some(value.trim().into()),
                &"output_base" => output_base = Some(value.trim().into()),
                &"workspace" => workspace_root = Some(value.trim().into()),
                _ => {}
            },
            _ => {}
        }
    });
    match (execroot, output_base, workspace_root) {
        (Some(execroot), Some(output_base), Some(workspace_root)) => Some(BazelInfo {
            workspace_root,
            execroot,
            output_base,
        }),
        _ => {
            eprintln!(
                "Couldn't find workspace_root, execroot or output_base in output:\n`{}`",
                info
            );
            None
        }
    }
}

pub fn get_bazel_info(workspace_dir: Option<&str>) -> Option<BazelInfo> {
    let mut raw_command = Command::new("bazel");
    let mut command = raw_command.arg("info");
    command = match workspace_dir {
        Some(d) => command.current_dir(d),
        None => command,
    };

    let output = command.output().ok()?;

    if !output.status.success() {
        return None;
    }

    let s = std::str::from_utf8(output.stdout.as_slice()).ok()?;

    parse_bazel_info(s)
}

#[cfg(test)]
mod tests {
    use super::parse_bazel_info;
    use super::BazelInfo;

    #[test]
    fn parses_info() {
        assert_eq!(
            parse_bazel_info(include_str!("info.txt")),
            Some(BazelInfo {
                workspace_root: "/home/user/dev/bazel/bazel".into(),
                execroot: "/home/user/.cache/bazel/_bazel_user/726bdc44ca84ffc53f631c27e313c4cf/execroot/io_bazel".into(),
                output_base: "/home/user/.cache/bazel/_bazel_user/726bdc44ca84ffc53f631c27e313c4cf".into()
            })
        )
    }
}
