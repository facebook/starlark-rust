#![no_main]

use std::hint::black_box;

use libfuzzer_sys::fuzz_target;
use starlark::environment::Globals;
use starlark::environment::Module;
use starlark::eval::Evaluator;
use starlark::syntax::AstModule;
use starlark::syntax::Dialect;

fn run_arbitrary_starlark(content: &str) -> anyhow::Result<()> {
    let ast: AstModule =
        AstModule::parse("hello_world.star", content.to_owned(), &Dialect::Standard)?;
    let globals: Globals = Globals::standard();
    let module: Module = Module::new();
    let mut eval: Evaluator = Evaluator::new(&module);
    let value = black_box(eval.eval_module(ast, &globals)?);
    _ = black_box(format!("{value:?}"));
    return Ok(());
}

fuzz_target!(|content: &str| {
    if let Err(e) = black_box(run_arbitrary_starlark(content)) {
        _ = black_box(format!("{e:?}"));
    }
});
