#!/usr/bin/env python3
"""Check felem_contract and snapshots of its three stages against integers."""
import ctypes
import itertools
import os
from pathlib import Path
import random
import subprocess
import tempfile

from generate import SOURCE, body
from generate_contract import contract_statements

P = 2**384 - 2**128 - 2**96 + 2**32 - 1
R = 2**56
U64, I64 = ctypes.c_uint64, ctypes.c_int64
Felem, SignedFelem = U64 * 7, I64 * 7


def compile_library(directory):
    source = SOURCE.read_text()
    contract_statements(source)
    fragment = body(source, "felem_contract")
    marker = "cond[0] ="
    fragment = fragment.replace(marker, "memcpy(first, tmp, sizeof(felem));\n" + marker, 1)
    marker = "a = cond[0] & (cond[1] | (cond[2] & (~cond[3] | cond[4])));"
    fragment = fragment.replace(marker, "memcpy(flags, cond, sizeof(int64_t) * 5);\n" + marker, 1)
    marker = "a = tmp[0] >> 63;"
    position = fragment.rindex(marker)
    fragment = fragment[:position] + "memcpy(subtracted, tmp, sizeof(felem));\n" + fragment[position:]
    content = """
#include <stdint.h>
#include <string.h>
#define NLIMBS 7
typedef uint64_t limb;
typedef limb felem[7];
void trace_contract(felem out, felem first, int64_t flags[5], int64_t subtracted[7], const felem in) {
""" + fragment + "\n}\n"
    cfile, library = directory / "contract.c", directory / "contract.so"
    cfile.write_text(content)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-shared", "-fPIC",
                    "-Wall", "-Wextra", "-Werror", "-fsanitize=undefined",
                    "-fno-sanitize-recover=all", str(cfile), "-o", str(library)], check=True)
    return ctypes.CDLL(str(library))


def limbs(value):
    return Felem(*[(value >> (56 * i)) % R for i in range(7)])


def value(words):
    return sum(int(word) << (56 * i) for i, word in enumerate(words))


def run(lib):
    rng, checks = random.Random(384384), 0
    cases = [0, 1, P-1, P, P+1, 2**384-1]
    cases += [2**384 + low for low in [0, 1, 2**32-2, 2**32-1, 2**56-1, 2**336-1]]
    for high, bit, middle, low, bottom in itertools.product(
            [2**255-2, 2**255-1], [0, 1], [0, 2**32-2, 2**32-1],
            [0, 1, 2**64-1], [0, 2**32-2, 2**32-1]):
        cases.append((high << 129) + (bit << 128) + (middle << 96) + (low << 32) + bottom)
    inputs = [limbs(n) for n in cases]
    for _ in range(512):
        inputs.append(Felem(*[rng.randrange(R) for _ in range(6)], rng.randrange(2**48 + 1)))

    def require(ok, label):
        nonlocal checks
        if not ok:
            raise AssertionError(label)
        checks += 1

    flags_seen = set()
    for a in inputs:
        out, first, flags, subtracted = Felem(), Felem(), (I64 * 5)(), SignedFelem()
        lib.trace_contract(out, first, flags, subtracted, a)
        n, f = value(a), value(first)
        require(f == n - (n // 2**384) * P, "first-stage value")
        require(all(x < R for x in first[:6]) and first[6] < 2**48, "first-stage bounds")
        expected = [f >> 129 == 2**255-1, (f >> 128) % 2 == 1,
                    (f >> 96) % 2**32 == 2**32-1, (f >> 32) % 2**64 == 0,
                    f % 2**32 == 2**32-1]
        require(list(flags) == [-int(p) for p in expected], "five condition masks")
        flags_seen.add(tuple(expected))
        needs = expected[0] and (expected[1] or (expected[2] and (not expected[3] or expected[4])))
        require(needs == (f >= P), "combined condition")
        require(value(subtracted) == f - (P if needs else 0), "conditional subtraction")
        require(value(out) == n % P, "final value")
        require(all(x < R for x in out[:6]) and out[6] < 2**48, "final bounds")
        twice = Felem()
        lib.trace_contract(twice, first, flags, subtracted, out)
        require(bytes(twice) == bytes(out), "idempotence")
    require(len(flags_seen) == 32, "all 32 condition combinations covered")
    print(f"{checks} contract C checks passed; all 32 condition combinations; UBSan enabled")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="p384-contract-") as directory:
        run(compile_library(Path(directory)))
