#!/usr/bin/env python3
"""Exercise extracted scalar multiplication against independent affine arithmetic."""
import ctypes
import os
from pathlib import Path
import random
import re
import subprocess
import tempfile

from check_c import P, U64, Felem, decode, encode, compile_library
from generate import SOURCE, body
from generate_scalar import UTIL

Point = Felem * 3
Table17 = Point * 17
Scalar = ctypes.c_uint8 * 48
G = (int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7", 16),
     int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", 16))


def add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    x, y = a
    u, v = b
    if x == u and (y + v) % P == 0:
        return None
    slope = ((3*x*x - 3) * pow(2*y, -1, P) if a == b else (v-y) * pow(u-x, -1, P)) % P
    r = (slope*slope-x-u) % P
    return r, (slope*(x-r)-y) % P


def mul(n, p):
    out = None
    while n:
        if n & 1:
            out = add(out, p)
        p = add(p, p)
        n >>= 1
    return out


def project(p, z=1):
    if p is None:
        return Point(encode(0), encode(0), encode(0))
    return Point(encode(p[0]*z*z % P), encode(p[1]*z**3 % P), encode(z))


def unproject(p):
    x, y, z = (decode(v) % P for v in p)
    if not z:
        return None
    zi = pow(z, -1, P)
    return x*zi**2 % P, y*zi**3 % P


def compile_scalar(directory):
    compile_library(directory)
    source, util = SOURCE.read_text(), UTIL.read_text()
    code = (directory / "arithmetic.c").read_text() + """
typedef uint8_t felem_bytearray[48];
typedef limb limb_aX __attribute__((__aligned__(1)));
static const limb bottom56bits = 0xffffffffffffff;
"""
    gmul = re.search(r"static const felem gmul\[16\]\[3\] = \{.*?\n\};", source, re.S)
    if gmul is None:
        raise ValueError("Missing generator table")
    code += gmul.group() + "\n"
    signatures = [
        (source, "void felem_to_bin48(uint8_t out[48], const felem in)"),
        (source, "int felem_is_zero_int(const void *in)"),
        (util, "void ossl_ec_GFp_nistp_points_make_affine_internal(size_t num, void *point_array, size_t felem_size, void *tmp_felems, void (*felem_one)(void *), int (*felem_is_zero)(const void *), void (*felem_assign)(void *, const void *), void (*felem_square)(void *, const void *), void (*felem_mul)(void *, const void *, const void *), void (*felem_inv)(void *, const void *), void (*felem_contract)(void *, const void *))"),
        (source, "void make_points_affine(size_t num, felem points[][3], felem tmp_felems[])"),
        (util, "void ossl_ec_GFp_nistp_recode_scalar_bits(unsigned char *sign, unsigned char *digit, unsigned char in)"),
        (source, "void select_point(const limb idx, unsigned int size, const felem pre_comp[][3], felem out[3])"),
        (source, "char get_bit(const felem_bytearray in, int i)"),
        (source, "void batch_mul(felem x_out, felem y_out, felem z_out, const felem_bytearray scalars[], const unsigned int num_points, const uint8_t *g_scalar, const int mixed, const felem pre_comp[][17][3], const felem g_pre_comp[16][3])"),
    ]
    for text, signature in signatures:
        name = signature.split("(")[0].split()[-1]
        code += signature + " {\n" + body(text, name) + "\n}\n"
    code += """
void test_batch(felem out[3], const felem_bytearray scalars[], unsigned int n,
                const uint8_t *gs, int mixed, const felem tables[][17][3]) {
    batch_mul(out[0], out[1], out[2], scalars, n, gs, mixed, tables, gmul);
}
void test_generator(unsigned int i, felem out[3]) {
    memcpy(out, gmul[i], sizeof(gmul[i]));
}
void test_finalize(uint8_t out[3][48], felem contracted[3], const felem in[3]) {
    for (unsigned int i = 0; i < 3; ++i) {
        felem_contract(contracted[i], in[i]);
        felem_to_bin48(out[i], contracted[i]);
    }
}
void test_precompute(felem table[17][3], const felem point[3]) {
    memset(table, 0, 17 * 3 * sizeof(felem));
    memcpy(table[1], point, 3 * sizeof(felem));
    for (unsigned int j = 2; j <= 16; ++j) {
        if (j & 1)
            point_add(table[j][0], table[j][1], table[j][2],
                      table[1][0], table[1][1], table[1][2], 0,
                      table[j-1][0], table[j-1][1], table[j-1][2]);
        else
            point_double(table[j][0], table[j][1], table[j][2],
                         table[j/2][0], table[j/2][1], table[j/2][2]);
    }
}
"""
    path, library = directory / "scalar.c", directory / "scalar.so"
    path.write_text(code)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-shared", "-fPIC",
                    "-Wall", "-Wextra", "-Werror", "-fsanitize=undefined",
                    "-fno-sanitize-recover=all", str(path), "-o", str(library)], check=True)
    lib = ctypes.CDLL(str(library))
    lib.get_bit.restype = ctypes.c_byte
    return lib


def run(lib):
    rng = random.Random(3845)
    checks = 0

    def require(condition, label):
        nonlocal checks
        if not condition:
            raise AssertionError(label)
        checks += 1

    for w in range(64):
        sign, digit = ctypes.c_uint8(), ctypes.c_uint8()
        lib.ossl_ec_GFp_nistp_recode_scalar_bits(ctypes.byref(sign), ctypes.byref(digit), w)
        value = digit.value * (-1 if sign.value else 1)
        require(value == (w+1)//2 - 32*(w//32) and digit.value <= 16, "Booth")

    for n in [0, 1, 2**383, 2**384-1, rng.getrandbits(384)]:
        bs = Scalar.from_buffer_copy(n.to_bytes(48, "little"))
        for i in range(-8, 393):
            require(lib.get_bit(bs, i) == ((n >> i) & 1 if 0 <= i < 384 else 0), "get_bit")
        total = 0
        for i in range(0, 381, 5):
            raw = sum(lib.get_bit(bs, i+j-1) << j for j in range(6))
            total += ((raw+1)//2 - 32*(raw//32)) << i
        require(total == n, "Booth reconstruction")

    basis = [mul(1 << (95*j), G) for j in range(4)]
    for idx in range(16):
        expected = None
        for j in range(4):
            if idx >> j & 1:
                expected = add(expected, basis[j])
        out = Point()
        lib.test_generator(idx, out)
        require(unproject(out) == expected, "builtin generator table")

    for size in (16, 17):
        table = (Point * size)(*[Point(*[Felem(*[rng.getrandbits(64) for _ in range(7)]) for _ in range(3)]) for _ in range(size)])
        for idx in range(32):
            out = Point()
            lib.select_point(U64(idx), size, table, out)
            require(bytes(out) == (bytes(table[idx]) if idx < size else bytes(Point())), "selection")

    points = [G, mul(7, G), None, mul(13, G)]
    dynamic = []
    for p in points:
        table = Table17()
        lib.test_precompute(table, project(p, rng.randrange(1, P)))
        for j in range(17):
            require(unproject(table[j]) == mul(j, p), "ordinary precomputation")
        dynamic.append(table)

    cases = [([], None), ([], 0), ([], 1), ([], 2**383), ([], 2**384-1)]
    for n in [0, 1, 15, 16, 17, 31, 32, 63, 2**379, 2**383, 2**384-1]:
        cases.extend([([n], None), ([n], rng.getrandbits(384))])
    cases.extend([([rng.getrandbits(384) for _ in range(k)], rng.getrandbits(384) if j % 2 else None)
                  for j in range(12) for k in (2, 4)])
    for scalars, gs in cases:
        scalar_bytes = (Scalar * len(scalars))(*[Scalar.from_buffer_copy(n.to_bytes(48, "little")) for n in scalars])
        generator = None if gs is None else Scalar.from_buffer_copy(gs.to_bytes(48, "little"))
        expected = None if gs is None else mul(gs, G)
        for n, p in zip(scalars, points):
            expected = add(expected, mul(n, p))
        for mixed in (0, 1):
            if mixed:
                tables = (Table17 * len(scalars))(*[Table17(*[project(mul(j, p)) for j in range(17)]) for p in points[:len(scalars)]])
            else:
                tables = (Table17 * len(scalars))(*dynamic[:len(scalars)])
            out = Point()
            lib.test_batch(out, scalar_bytes, len(scalars), generator, mixed, tables)
            require(unproject(out) == expected, f"batch_mul/{mixed}/{scalars}/{gs}")
            contracted, encoded = Point(), (Scalar * 3)()
            lib.test_finalize(encoded, contracted, out)
            x, y, z = (int.from_bytes(bytes(bs), "little") for bs in encoded)
            result = None
            if z % P:
                zi = pow(z, -1, P)
                result = x*zi**2 % P, y*zi**3 % P
            require(result == expected and all(v < P for v in (x, y, z)), "canonical scalar output")
    print(f"Scalar C differential checks: {checks}; UBSan enabled")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="p384-scalar-") as tmp:
        run(compile_scalar(Path(tmp)))
