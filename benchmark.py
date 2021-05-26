# Copyright 2018 The Starlark in Rust Authors.
# Copyright (c) Facebook, Inc. and its affiliates.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Python: python benchmark.py
# Rust: starlark benchmark.py

# Python = 4.35s, Rust = 0.72s
def benchmark1():
    for _x in range(100000000):
        pass


# Python = 6.08s, Rust = 2.35s
def benchmark2():
    y = 3
    for _x in range(100000000):
        y = y * 1
    return y


# Python = 7.04s, Rust = 8.4s
def benchmark3():
    y = 0
    xs = []
    for _x in range(100000000):
        y = len(xs)
    return y


def op4(_x):
    pass


# Python = 9.85s, Rust = 8.4s
def benchmark4():
    y = 0
    for x in range(100000000):
        op4(x)
    return y


print(benchmark4())
