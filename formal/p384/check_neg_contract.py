#!/usr/bin/env python3
"""Reproduce the false felem_neg comment contract in compiled C."""
from pathlib import Path
import tempfile

from check_c import Felem, P, compile_library, decode


def main():
    a = Felem(0, 2**60 - 2**52 - 2**4 + 1, 0, 0, 0, 0, 0)
    if not all(v < 2**60 - 2**29 for v in a):
        raise AssertionError("Witness violates the stated input bound")
    with tempfile.TemporaryDirectory(prefix="p384-neg-contract-") as directory:
        lib = compile_library(Path(directory))
        out = Felem()
        lib.felem_neg(out, a)
        residue = (decode(out) + decode(a)) % P
        if out[1] != 2**64 - 1 or residue != 2**120:
            raise AssertionError("The recorded counterexample no longer matches C")
        print("Confirmed: felem_neg comment admits an incorrect input")
        print(f"in[1]={a[1]}, out[1]={out[1]}")
        print(f"(out+in) mod p={residue}; expected 0")
        lib.felem_neg(out, Felem())
        if out[0] <= 2**60:
            raise AssertionError("The recorded output-bound counterexample changed")
        print(f"Confirmed: zero input gives out[0]={out[0]} > 2^60")


if __name__ == "__main__":
    main()
