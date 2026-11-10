#!/usr/bin/env python3
"""Compare compiled C arithmetic with Python integer arithmetic."""
import ctypes
import os
from pathlib import Path
import random
import subprocess
import tempfile

from generate import SOURCE, body

P = 2**384 - 2**128 - 2**96 + 2**32 - 1
MASK = 2**56 - 1
U64 = ctypes.c_uint64
Felem = U64 * 7
Wide = U64 * 26


def decode(a):
    return sum(int(v) << (56*i) for i, v in enumerate(a))


def encode(n):
    return Felem(*[(n >> (56*i)) & MASK for i in range(7)])


def reduced(a):
    return all(v < 2**56 for v in a[:6]) and a[6] <= 2**48


def compile_library(directory):
    source = SOURCE.read_text()
    signatures = [
        "void felem_one(felem out)",
        "void felem_assign(felem out, const felem in)",
        "void felem_sum64(felem out, const felem in)",
        "void felem_scalar(felem out, const felem in, limb scalar)",
        "void felem_scalar64(felem out, limb scalar)",
        "void felem_scalar128(widefelem out, limb scalar)",
        "void felem_neg(felem out, const felem in)",
        "void felem_diff64(felem out, const felem in)",
        "void felem_diff_128_64(widefelem out, const felem in)",
        "void felem_diff128(widefelem out, const widefelem in)",
        "void felem_square_ref(widefelem out, const felem in)",
        "void felem_mul_ref(widefelem out, const felem in1, const felem in2)",
        "void felem_reduce_ref(felem out, const widefelem in)",
        "void felem_square_reduce_ref(felem out, const felem in)",
        "void felem_mul_reduce_ref(felem out, const felem in1, const felem in2)",
        "void felem_inv(felem out, const felem in)",
        "limb felem_is_zero(const felem in)",
        "void felem_contract(felem out, const felem in)",
        "void point_double(felem x_out, felem y_out, felem z_out, const felem x_in, const felem y_in, const felem z_in)",
        "void copy_conditional(felem out, const felem in, limb mask)",
        "void point_add(felem x3, felem y3, felem z3, const felem x1, const felem y1, const felem z1, const int mixed, const felem x2, const felem y2, const felem z2)",
    ]
    content = """
#include <stdint.h>
#include <string.h>
#define NLIMBS 7
typedef uint64_t limb;
typedef __uint128_t uint128_t;
typedef uint128_t widelimb;
typedef limb felem[7];
typedef widelimb widefelem[13];
#define felem_square felem_square_ref
#define felem_mul felem_mul_ref
#define felem_reduce felem_reduce_ref
#define felem_square_reduce felem_square_reduce_ref
#define felem_mul_reduce felem_mul_reduce_ref
"""
    for signature in signatures:
        name = signature.split("(")[0].split()[-1]
        content += signature + " {\n" + body(source, name) + "\n}\n"
    content += """
void test_reduce(felem out, const uint64_t raw[26]) {
    widefelem a;
    for (int i = 0; i < 13; ++i)
        a[i] = (widelimb)raw[2*i] | ((widelimb)raw[2*i+1] << 64);
    felem_reduce_ref(out, a);
}
void test_mul(uint64_t raw[26], const felem a, const felem b) {
    widefelem out;
    felem_mul_ref(out, a, b);
    for (int i = 0; i < 13; ++i) {
        raw[2*i] = (uint64_t)out[i];
        raw[2*i+1] = (uint64_t)(out[i] >> 64);
    }
}
"""
    cfile, library = directory / "arithmetic.c", directory / "arithmetic.so"
    cfile.write_text(content)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-shared", "-fPIC",
                    "-Wall", "-Wextra", "-Werror", "-fsanitize=undefined",
                    "-fno-sanitize-recover=all", str(cfile), "-o", str(library)], check=True)
    lib = ctypes.CDLL(str(library))
    lib.felem_is_zero.restype = U64
    return lib


def run(lib):
    rng = random.Random(384)
    checks = 0
    def require(condition, label):
        nonlocal checks
        if not condition:
            raise AssertionError(label)
        checks += 1

    for _ in range(256):
        a = [rng.randrange(2**128 - 2**125) for _ in range(13)]
        raw = Wide(*[part for value in a for part in (value % 2**64, value >> 64)])
        out = Felem()
        lib.test_reduce(out, raw)
        require(decode(out) % P == decode(a) % P and reduced(out), "reduce")
        x, y = [Felem(*[rng.randrange(2**61) for _ in range(7)]) for _ in range(2)]
        product = Wide()
        lib.test_mul(product, x, y)
        result = [product[2*i] + (product[2*i+1] << 64) for i in range(13)]
        require(decode(result) == decode(x) * decode(y), "mul")
        lib.felem_mul_reduce_ref(out, x, y)
        require(decode(out) % P == decode(x) * decode(y) % P and reduced(out), "mul_reduce")
        lib.felem_square_reduce_ref(out, x)
        require(decode(out) % P == decode(x)**2 % P and reduced(out), "square_reduce")

    cases = [0, 1, P-1, P, P+1, 2**384-1, 2**384, 2**384 + 2**336 - 1]
    cases += [rng.randrange(P) for _ in range(128)]
    for n in cases:
        a, out = encode(n), Felem()
        lib.felem_contract(out, a)
        require(decode(out) == n % P, "contract")
        require(lib.felem_is_zero(a) == (2**64-1 if n % P == 0 else 0), "is_zero")
        lib.felem_inv(out, a)
        require(decode(out) % P == pow(n, P-2, P) and reduced(out), "inv")

    gx = int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7", 16)
    gy = int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", 16)
    def add(a, b):
        if a is None: return b
        if b is None: return a
        x, y = a
        u, v = b
        if x == u and (y + v) % P == 0: return None
        slope = ((3*x*x-3) * pow(2*y, -1, P) if a == b else (v-y)*pow(u-x, -1, P)) % P
        r = (slope*slope-x-u) % P
        return r, (slope*(x-r)-y) % P
    def project(a):
        z = rng.randrange(1, P)
        if a is None: return (encode(0), encode(0), encode(0))
        return encode(a[0]*z*z % P), encode(a[1]*z**3 % P), encode(z)
    def unproject(a):
        x, y, z = [decode(v) % P for v in a]
        if not z: return None
        zi = pow(z, -1, P)
        return x*zi**2 % P, y*zi**3 % P
    points = [None, (gx, gy)]
    for _ in range(8): points.append(add(points[-1], (gx, gy)))
    for a in points:
        pa, out = project(a), (Felem(), Felem(), Felem())
        lib.point_double(*out, *pa)
        require(unproject(out) == add(a, a), "point_double")
        for b in points + ([None] if a is None else [(a[0], -a[1] % P)]):
            for mixed in (0, 1):
                pb = project(b) if not mixed else ((encode(b[0]), encode(b[1]), encode(1)) if b else project(None))
                lib.point_add(*out, *pa, mixed, *pb)
                require(unproject(out) == add(a, b), "point_add")
    print(f"C differential checks: {checks}; UBSan enabled")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="p384-check-") as tmp:
        run(compile_library(Path(tmp)))
