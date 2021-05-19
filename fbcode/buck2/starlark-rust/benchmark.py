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


# Python = 7.04s, Rust = 21.4s
def benchmark3():
    y = 0
    xs = []
    for _x in range(100000000):
        y = len(xs)
    return y


print(benchmark3())
