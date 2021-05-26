#!/usr/bin/env python3

import argparse
import os
import subprocess
import tempfile
import time
from pathlib import Path


def compile_starlark():
    if "CARGO_TARGET_DIR" not in os.environ:
        raise Exception("Must set CARGO_TARGET_DIR, so we can find Cargo outputs")
    print("Building starlark")
    subprocess.run("cargo build --release --bin=starlark", shell=True, check=True)
    return os.environ["CARGO_TARGET_DIR"] + "/release/starlark"


def generate_benchmarks(dir):
    benchmark = Path(__file__).parent.joinpath("benchmark.py")

    with open(benchmark, "r") as file:
        src = file.read()

    # Find all the benchmarks
    benchmarks = [
        x[4:-3]
        for x in src.splitlines()
        if x.startswith("def benchmark") and x.endswith("():")
    ]

    outputs = {}
    for benchmark in benchmarks:
        # Whichever one is committed, make sure we switch it for this one
        src2 = src
        for x in benchmarks:
            src2 = src2.replace("print(" + x + "())", "print(" + benchmark + "())")
        output = Path(dir).joinpath(benchmark + ".py")
        with open(output, "w") as out:
            out.write(src2)
        outputs[benchmark] = output
    return outputs


def absh(a, b, repeat):
    a_time = 0
    b_time = 0
    runs = 0

    # Run a/b repeatedly, ignoring the first loop around
    for i in range(repeat + 1):
        start_time = time.time()
        subprocess.run(a, check=True, capture_output=True)
        middle_time = time.time()
        subprocess.run(b, check=True, capture_output=True)
        end_time = time.time()

        if i != 0:
            a_time += middle_time - start_time
            b_time += end_time - middle_time
            runs += 1
        print(".", end="", flush=True)

    print("")
    return (a_time / runs, b_time / runs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repeat",
        default=6,
        type=int,
        help="How many times to repeat",
    )
    args = parser.parse_args()

    starlark = compile_starlark()
    with tempfile.TemporaryDirectory() as dir:
        benchmarks = generate_benchmarks(dir)
        for name, file in benchmarks.items():
            print("Benchmarking: " + name + " ", end="", flush=True)
            (py, st) = absh(("python3", file), (starlark, file), repeat=args.repeat)
            print("Python3 {:.2f}s, Starlark Rust {:.2f}s".format(py, st))


if __name__ == "__main__":
    main()
