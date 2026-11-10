#!/usr/bin/env python3
"""Test current C conversion bodies; allocation helpers are local test doubles."""
import ctypes
import os
from pathlib import Path
import random
import subprocess
import tempfile

from check_interfaces import ROOT, check
from generate import body

U8, U64 = ctypes.c_uint8, ctypes.c_uint64
Bytes48, Felem = U8 * 48, U64 * 7


def compile_library(directory):
    ec = (ROOT / "crypto/ec/ecp_nistp384.c").read_text()
    bn = (ROOT / "crypto/bn/bn_lib.c").read_text()
    content = r"""
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#define BN_BITS2 64
#define BN_BYTES 8
#define BN_MASK2 UINT64_MAX
#define BN_FLG_CONSTTIME 4
#define BN_FLG_FIXED_TOP 0
#define bn_check_top(a) ((void)(a))
#define bn_pollute(a) ((void)(a))
#define ossl_unlikely(a) (a)
#define ossl_likely(a) (a)
#define ERR_LIB_EC 0
#define EC_R_BIGNUM_OUT_OF_RANGE 0
#define ERR_raise(a, b) ((void)0)
typedef uint64_t BN_ULONG;
typedef struct { BN_ULONG *d; int top, dmax, neg, flags; } BIGNUM;
typedef uint64_t limb;
typedef limb limb_aX __attribute__((__aligned__(1)));
typedef limb felem[7];
typedef uint8_t felem_bytearray[48];
static const limb bottom56bits = UINT64_C(0xffffffffffffff);
typedef enum { BIG, LITTLE } endianness_t;
typedef enum { SIGNED, UNSIGNED } signedness_t;
static int fail_allocation;
static unsigned int constant_time_eq_int(int a, int b) { return 0u - (a == b); }
static BIGNUM *BN_new(void) {
    if (fail_allocation) return NULL;
    return calloc(1, sizeof(BIGNUM));
}
static void BN_clear(BIGNUM *a) {
    if (a->dmax) memset(a->d, 0, (size_t)a->dmax * 8);
    a->top = a->neg = 0;
}
static BIGNUM *bn_wexpand(BIGNUM *a, int n) {
    if (n <= a->dmax) return a;
    if (fail_allocation) return NULL;
    BN_ULONG *p = calloc((size_t)n, 8);
    if (!p) return NULL;
    if (a->top) memcpy(p, a->d, (size_t)a->top * 8);
    free(a->d); a->d = p; a->dmax = n;
    return a;
}
static void BN_free(BIGNUM *a) { if (a) { free(a->d); free(a); } }
"""
    bn_signatures = [
        "int BN_is_zero(const BIGNUM *a)",
        "int BN_is_negative(const BIGNUM *a)",
        "int BN_num_bits_word(BN_ULONG l)",
        "int bn_num_bits_consttime(const BIGNUM *a)",
        "int BN_num_bits(const BIGNUM *a)",
        "void bn_correct_top(BIGNUM *a)",
        "BIGNUM *bin2bn(const unsigned char *s, int len, BIGNUM *ret, endianness_t endianness, signedness_t signedness)",
        "int bn2binpad(const BIGNUM *a, unsigned char *to, int tolen, endianness_t endianness, signedness_t signedness)",
        "BIGNUM *BN_lebin2bn(const unsigned char *s, int len, BIGNUM *ret)",
        "int BN_bn2lebinpad(const BIGNUM *a, unsigned char *to, int tolen)",
    ]
    ec_signatures = [
        "void bin48_to_felem(felem out, const uint8_t in[48])",
        "void felem_to_bin48(uint8_t out[48], const felem in)",
        "int BN_to_felem(felem out, const BIGNUM *bn)",
        "BIGNUM *felem_to_BN(BIGNUM *out, const felem in)",
    ]
    for source, signatures in ((bn, bn_signatures), (ec, ec_signatures)):
        for signature in signatures:
            name = signature.split("(")[0].split()[-1].lstrip("*")
            content += signature + " {\n" + body(source, name) + "\n}\n"
    content += r"""
int test_export(uint8_t *out, const uint64_t *words, int capacity, int top, int neg, int flags, int n) {
    BIGNUM a = { (BN_ULONG *)words, top, capacity, neg, flags };
    return BN_bn2lebinpad(&a, out, n);
}
int test_bn_to_felem(felem out, const uint64_t *words, int capacity, int top, int neg, int flags) {
    BIGNUM a = { (BN_ULONG *)words, top, capacity, neg, flags };
    return BN_to_felem(out, &a);
}
int test_import(uint64_t *out, int *top, int *neg, const uint8_t *in, int len, int oldneg, int fail) {
    BIGNUM *a = BN_new();
    if (!a || !bn_wexpand(a, 1)) abort();
    a->d[0] = 7; a->top = 1; a->neg = oldneg;
    fail_allocation = fail;
    BIGNUM *r = BN_lebin2bn(in, len, a);
    fail_allocation = 0;
    if (!r) { BN_free(a); return 0; }
    memset(out, 0, 7 * 8);
    memcpy(out, r->d, (size_t)r->top * 8);
    *top = r->top; *neg = r->neg;
    BN_free(a);
    return 1;
}
int test_felem_to_bn(uint64_t *out, int *top, int *neg, const felem in, int oldneg, int fail) {
    BIGNUM *a = BN_new();
    if (!a || !bn_wexpand(a, 1)) abort();
    a->d[0] = 7; a->top = 1; a->neg = oldneg;
    fail_allocation = fail;
    BIGNUM *r = felem_to_BN(a, in);
    fail_allocation = 0;
    if (!r) { BN_free(a); return 0; }
    memset(out, 0, 7 * 8);
    memcpy(out, r->d, (size_t)r->top * 8);
    *top = r->top; *neg = r->neg;
    BN_free(a);
    return 1;
}
"""
    cfile, library = directory / "interfaces.c", directory / "interfaces.so"
    cfile.write_text(content)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-shared", "-fPIC",
                    "-Wall", "-Wextra", "-Werror", "-fsanitize=undefined",
                    "-fno-sanitize-recover=all", str(cfile), "-o", str(library)], check=True)
    return ctypes.CDLL(str(library))


def run(lib):
    rng, checks = random.Random(38448), 0

    def require(condition, label):
        nonlocal checks
        if not condition:
            raise AssertionError(label)
        checks += 1

    values = [0, 1, 2**48-1, 2**56-1, 2**64-1, 2**384-1, 2**384]
    values += [rng.randrange(2**384) for _ in range(256)]
    for value in values:
        top = (value.bit_length() + 63) // 64
        for capacity in sorted({top, top + 3}):
            words = (U64 * capacity)(*[
                (value >> (64*i)) % 2**64 if i < top else rng.getrandbits(64)
                for i in range(capacity)])
            for flags in (0, 4):
                guarded = (U8 * 80)(*[0xA5] * 80)
                outptr = ctypes.cast(ctypes.byref(guarded, 16), ctypes.POINTER(U8))
                result = lib.test_export(outptr, words, capacity, top, 0, flags, 48)
                expected = 48 if value < 2**384 else -1
                require(result == expected, "BN_bn2lebinpad return")
                require(bytes(guarded[:16]) + bytes(guarded[64:]) == bytes([0xA5]*32), "export frame")
                if result == 48:
                    require(bytes(guarded[16:64]) == value.to_bytes(48, "little"), "export bytes")
                else:
                    require(bytes(guarded) == bytes([0xA5]*80), "export failure frame")
                limbs = Felem(*[0xA5] * 7)
                for neg in (0, 1):
                    result = lib.test_bn_to_felem(limbs, words, capacity, top, neg, flags)
                    require(result == int(not neg and value < 2**384), "BN_to_felem return")
                    if result:
                        require(sum(int(x) << (56*i) for i, x in enumerate(limbs)) == value,
                                "BN_to_felem value")
        if value >= 2**384:
            continue
        raw, limbs = Bytes48.from_buffer_copy(value.to_bytes(48, "little")), Felem()
        lib.bin48_to_felem(limbs, raw)
        require(sum(int(x) << (56*i) for i, x in enumerate(limbs)) == value, "deserialize")
        guarded = (U8 * 80)(*[0xA5] * 80)
        outptr = ctypes.cast(ctypes.byref(guarded, 16), ctypes.POINTER(U8))
        lib.felem_to_bin48(outptr, limbs)
        require(bytes(guarded[16:64]) == bytes(raw), "serialize")
        require(bytes(guarded[:16]) + bytes(guarded[64:]) == bytes([0xA5]*32), "serialize frame")
        for oldneg in (0, 1):
            words, topout, negout = (U64 * 7)(), ctypes.c_int(), ctypes.c_int()
            result = lib.test_import(words, ctypes.byref(topout), ctypes.byref(negout), raw, 48, oldneg, 0)
            require(result == 1, "BN_lebin2bn success")
            require(sum(int(x) << (64*i) for i, x in enumerate(words)) == value, "BN_lebin2bn value")
            require(negout.value == (oldneg if value == 0 else 0), "BN_lebin2bn zero reuse sign")
            result = lib.test_felem_to_bn(words, ctypes.byref(topout), ctypes.byref(negout), limbs, oldneg, 0)
            require(result == 1 and sum(int(x) << (64*i) for i, x in enumerate(words)) == value,
                    "felem_to_BN value")
        words, topout, negout = (U64 * 7)(), ctypes.c_int(), ctypes.c_int()
        result = lib.test_import(words, ctypes.byref(topout), ctypes.byref(negout), raw, 48, 0, 1)
        require(result == int(value < 2**64), "import allocation failure")

    require(lib.test_import((U64 * 7)(), ctypes.byref(ctypes.c_int()), ctypes.byref(ctypes.c_int()),
                            Bytes48(), -1, 0, 0) == 0, "negative input length")
    print(f"{checks} C interface differential checks passed (local allocation helpers)")
    print("Confirmed: importing 48 zero bytes into a reused negative BIGNUM leaves neg=1")


if __name__ == "__main__":
    check()
    with tempfile.TemporaryDirectory(prefix="p384-interfaces-") as directory:
        run(compile_library(Path(directory)))
