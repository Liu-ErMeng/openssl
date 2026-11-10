#!/usr/bin/env python3
"""Compare current BN length/normalization bodies and CT helpers with integers."""
import ctypes
import os
from pathlib import Path
import random
import subprocess
import tempfile

from check_interfaces import ROOT, check
from generate import body
from generate_bn_bits import stages

U32, U64, U8 = ctypes.c_uint32, ctypes.c_uint64, ctypes.c_uint8


def compile_library(directory):
    source = (ROOT / "crypto/bn/bn_lib.c").read_text()
    header = (ROOT / "include/internal/constant_time.h").read_text()
    stages(source)
    content = r"""
#include <stdint.h>
#include <string.h>
#include <limits.h>
_Static_assert(sizeof(int) == 4 && sizeof(unsigned int) == 4, "32-bit int required");
_Static_assert(sizeof(size_t) == 8, "64-bit size_t required");
#define BN_BITS2 64
#define BN_BYTES 8
#define BN_MASK2 UINT64_MAX
#define BN_FLG_CONSTTIME 4
#define BN_FLG_FIXED_TOP 0
#define bn_check_top(a) ((void)(a))
#define bn_pollute(a) ((void)(a))
#define ossl_unlikely(a) (a)
#define ossl_likely(a) (a)
typedef uint64_t BN_ULONG;
typedef struct { BN_ULONG *d; int top, dmax, neg, flags; } BIGNUM;
typedef enum { BIG, LITTLE } endianness_t;
typedef enum { SIGNED, UNSIGNED } signedness_t;
"""
    functions = [
        (header, "unsigned int constant_time_msb(unsigned int a)"),
        (header, "unsigned int constant_time_is_zero(unsigned int a)"),
        (header, "unsigned int constant_time_eq(unsigned int a, unsigned int b)"),
        (header, "unsigned int constant_time_eq_int(int a, int b)"),
        (source, "int BN_is_zero(const BIGNUM *a)"),
        (source, "int BN_num_bits_word(BN_ULONG l)"),
        (source, "int bn_num_bits_consttime(const BIGNUM *a)"),
        (source, "int BN_num_bits(const BIGNUM *a)"),
        (source, "void bn_correct_top(BIGNUM *a)"),
        (source, "int bn2binpad(const BIGNUM *a, unsigned char *to, int tolen, endianness_t endianness, signedness_t signedness)"),
        (source, "int BN_bn2lebinpad(const BIGNUM *a, unsigned char *to, int tolen)"),
    ]
    for text, signature in functions:
        name = signature.split("(")[0].split()[-1]
        content += signature + " {\n" + body(text, name) + "\n}\n"
    content += r"""
int test_bits(const uint64_t *words, int capacity, int top, int flags) {
    BIGNUM a = { (BN_ULONG *)words, top, capacity, 0, flags };
    return BN_num_bits(&a);
}
void test_normalize(const uint64_t *words, int capacity, int *top, int *neg, int *flags) {
    BIGNUM a = { (BN_ULONG *)words, *top, capacity, *neg, *flags };
    bn_correct_top(&a);
    *top = a.top; *neg = a.neg; *flags = a.flags;
}
int test_export(uint8_t *out, const uint64_t *words, int capacity, int top, int flags, int n) {
    BIGNUM a = { (BN_ULONG *)words, top, capacity, 0, flags };
    return BN_bn2lebinpad(&a, out, n);
}
"""
    cfile, library = directory / "bn-length.c", directory / "bn-length.so"
    cfile.write_text(content)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-shared", "-fPIC",
                    "-Wall", "-Wextra", "-Werror", "-fsanitize=undefined",
                    "-fno-sanitize-recover=all", str(cfile), "-o", str(library)], check=True)
    lib = ctypes.CDLL(str(library))
    lib.BN_num_bits_word.argtypes = [U64]
    lib.constant_time_eq_int.argtypes = [ctypes.c_int, ctypes.c_int]
    lib.constant_time_eq_int.restype = U32
    lib.constant_time_is_zero.argtypes = [U32]
    lib.constant_time_is_zero.restype = U32
    return lib


def run(lib):
    rng, checks = random.Random(6432384), 0

    def require(ok, label):
        nonlocal checks
        if not ok:
            raise AssertionError(label)
        checks += 1

    release_words = (U64 * 1)(1)
    release_top, release_neg, release_flags = ctypes.c_int(1), ctypes.c_int(0), ctypes.c_int(0x10004)
    lib.test_normalize(release_words, 1, ctypes.byref(release_top), ctypes.byref(release_neg),
                       ctypes.byref(release_flags))
    require(release_flags.value == 0x10004, "release normalization preserves flag bit 16")

    words = [0, 2**64-1]
    words += [value for bit in range(64) for value in {2**bit-1, 2**bit, min(2**bit+1, 2**64-1)}]
    words += [rng.getrandbits(64) for _ in range(1024)]
    for word in words:
        require(lib.BN_num_bits_word(word) == word.bit_length(), "BN_num_bits_word")
        low = word % 2**32
        require(lib.constant_time_is_zero(low) == (2**32-1 if low == 0 else 0), "CT zero")
        for other in (low, rng.getrandbits(32)):
            a, b = ctypes.c_int(low).value, ctypes.c_int(other).value
            require(lib.constant_time_eq_int(a, b) == (2**32-1 if a == b else 0), "CT equality")

    values = [0, 1, 2**64-1, 2**64, 2**384-1, 2**384, 2**512-1]
    values += [rng.getrandbits(rng.randrange(1, 1025)) for _ in range(128)]
    for value in values:
        actual_top = (value.bit_length() + 63) // 64
        capacity = actual_top + rng.randrange(1, 6)
        for top in sorted({actual_top, capacity}):
            data = (U64 * capacity)(*[
                (value >> (64*i)) % 2**64 if i < actual_top else 0 if i < top else rng.getrandbits(64)
                for i in range(capacity)])
            raw_bits = 0 if top == 0 else 64 * (top-1) + int(data[top-1]).bit_length()
            for flags in (0, 4, 0x10000, 0x10004):
                require(lib.test_bits(data, capacity, top, flags) == raw_bits, "BN_num_bits raw/fixed top")
                for old_neg in (0, 1):
                    t, neg, f = ctypes.c_int(top), ctypes.c_int(old_neg), ctypes.c_int(flags)
                    snapshot = bytes(data)
                    lib.test_normalize(data, capacity, ctypes.byref(t), ctypes.byref(neg), ctypes.byref(f))
                    require(t.value == actual_top, "normalized top")
                    require(neg.value == (0 if value == 0 else old_neg), "normalized sign")
                    require(f.value == flags and bytes(data) == snapshot, "normalization frame/flags")
                for length in (-1, 0, 1, 47, 48, 49):
                    guarded = (U8 * 96)(*[0xA5] * 96)
                    output = ctypes.cast(ctypes.byref(guarded, 16), ctypes.POINTER(U8))
                    result = lib.test_export(output, data, capacity, top, flags, length)
                    accept = length >= 0 and value < 2**(8*max(length, 0))
                    require(result == (length if accept else -1), "length guard and retry")
                    if accept:
                        require(bytes(guarded[16:16+length]) == value.to_bytes(length, "little"), "export value")
                        require(bytes(guarded[:16]) + bytes(guarded[16+length:]) == bytes([0xA5]*(96-length)),
                                "export frame")
                    else:
                        require(bytes(guarded) == bytes([0xA5]*96), "rejection frame")
    print(f"{checks} BN length C checks passed; actual CT helpers; fixed-top retries; UBSan enabled")


if __name__ == "__main__":
    check()
    with tempfile.TemporaryDirectory(prefix="p384-bn-length-") as directory:
        run(compile_library(Path(directory)))
