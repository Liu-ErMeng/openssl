#!/usr/bin/env python3
"""Check the reviewed source snapshot for the hand-translated interface loops."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate import body

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MANIFEST = HERE / "interface-sources.json"
FUNCTIONS = {
    "crypto/ec/ecp_nistp384.c": [
        "bin48_to_felem", "felem_to_bin48", "BN_to_felem", "felem_to_BN",
    ],
    "crypto/bn/bn_lib.c": [
        "bin2bn", "bn2binpad", "BN_lebin2bn", "BN_bn2lebinpad",
        "BN_is_negative", "BN_is_zero", "BN_num_bits_word",
        "bn_num_bits_consttime", "BN_num_bits", "bn_correct_top",
        "bn_expand_internal",
    ],
    "include/internal/constant_time.h": [
        "constant_time_msb", "constant_time_is_zero", "constant_time_eq", "constant_time_eq_int",
    ],
}
HEADERS = ("crypto/bn/bn_local.h", "include/openssl/bn.h")


def snapshot(sources=None):
    result = {}
    for path, functions in FUNCTIONS.items():
        source = (sources or {}).get(path)
        if source is None:
            source = (ROOT / path).read_text()
        source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
        result[path] = {
            name: hashlib.sha256(re.sub(r"\s+", "", body(source, name)).encode()).hexdigest()
            for name in functions
        }
    for path in HEADERS:
        source = (sources or {}).get(path)
        if source is None:
            source = (ROOT / path).read_text()
        source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
        result[path] = {"header": hashlib.sha256(re.sub(r"\s+", "", source).encode()).hexdigest()}
    return result


def check(sources=None):
    if snapshot(sources) != json.loads(MANIFEST.read_text())["functions"]:
        raise ValueError("Interface source changed; review the hand translation and proofs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="record a reviewed source snapshot")
    args = parser.parse_args()
    if args.write:
        MANIFEST.write_text(json.dumps({
            "boundary": "Hand-translated value loops; no verified C frontend or heap semantics",
            "target": "Little endian; uint64_t limbs; BN_BYTES=8; size_t=64; int=32; non-e2k; BN_DEBUG disabled",
            "functions": snapshot(),
        }, indent=2) + "\n")
    else:
        check()
        print("Reviewed interface source snapshot matches")


if __name__ == "__main__":
    main()
