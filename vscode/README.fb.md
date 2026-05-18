### Starlark VS Code Extension

Our team maintains a generic Starlark VS Code extension that gives IDE support
for build files and .bzl files. It is under active development and will be
gaining features regularly.

There are two copies of the VS Code Extension. One is for internal use, and is
at `fbsource/vscode/vscode-extensions/starlark`, and the other, for OSS use, is
at `starlark-rust/vscode`.

The key difference is that the internal version integrates with our internal
VSCode infrastructure, and has some extra feature gating, interaction with the
old buck extension, and uses our metrics framework. It also has some different
setting defaults, like using `buck2` as the LSP binary instead of `starlark`

This plugin works by talking to `buck2 lsp` over stdin/stderr. As features are
implemented in buck2's LSP server, they will automatically start working in the
plugin.

If trying to build and install the OSS plugin on an eden FS, it can help to add
a redirect to the vscode plugin's node_modules directory:

```shell
eden redirect add fbcode/buck2/starlark-rust/vscode/node_modules bind
```

To use the internal plugin for development, see the README in
`fbsource/vscode/vscode-extensions/starlark`.

To use the OSS plugin for development, follow the instructions at
`starlark-rust/vscode/README.md`, or the abbreviated ones here.

- `cd starlark-rust/vscode && npm install && npm install vsce && npm exec vsce package`
- In VS Code, go to Extensions, click on the "..." button in the Extensions bar,
  select "Install from VSIX" and then select the `starlark-1.0.0.vsix` file at
  `$FBCODE/buck2/starlark-rust/vscode/starlark-1.0.0.vsix`
- Update the extension settings to point to `buck2` for `starlark.lspPath`, and
  `["lsp"]` for `starlark.lspArguments`. This can be done in the VS Code UI by
  going to the extension's settings panel.

If you want to use a local build of buck2, just change the path to
`$FBCODE/buck2/scripts/buck2_lsp.sh` and unset `starlark.lspArguments`.

NOTE: If you're seeing slightly confusing behavior, make sure that you're using
"Starlark" as the language for files that you're editing.
