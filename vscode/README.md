# Starlark VS Code LSP extension

Based on a combination of:

* Tutorial at https://code.visualstudio.com/api/language-extensions/language-server-extension-guide
* Code for the tutorial at https://github.com/microsoft/vscode-extension-samples/tree/master/lsp-sample
* Syntax files from https://github.com/phgn0/vscode-starlark (which are the Microsoft Python ones with minor tweaks)

## Debugging

- Run `npm install` in this folder. This installs all necessary npm modules in both the client and server folder
- Open VS Code on this folder.
- Press Ctrl+Shift+B to compile the client and server.
- Switch to the Debug viewlet.
- Select `Launch Client` from the drop down.
- Run the launch config.

## Installing

- Run `npm install vsce`
- Run `npm exec vsce package`
- In VS Code, go to Extensions, ..., Install from VSIX and select `starlark-1.0.0.vsix`
- Build Starlark binary and put it on your `$PATH`, e.g. `cd buck2 && cargo build --bin=starlark && cp $CARGO_TARGET_DIR/debug/starlark ~/.cargo/bin/starlark`.
