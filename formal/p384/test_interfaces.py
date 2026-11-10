#!/usr/bin/env python3
"""Reject semantic changes in the interface source snapshot."""
import unittest

from check_interfaces import ROOT, check


class InterfaceBoundary(unittest.TestCase):
    def reject(self, path, old, new):
        source = (ROOT / path).read_text()
        self.assertIn(old, source)
        with self.assertRaises(ValueError):
            check({path: source.replace(old, new, 1)})

    def test_snapshot_matches(self):
        check()

    def test_export_mask(self):
        self.reject("crypto/bn/bn_lib.c", "mask = 0 - ((j - atop)", "mask = 0 - ((j + atop)")

    def test_export_cursor(self):
        self.reject("crypto/bn/bn_lib.c", "i += (i - lasti)", "i += (i + lasti)")

    def test_import_pack(self):
        self.reject("crypto/bn/bn_lib.c", "l |= (byte << m);", "l ^= (byte << m);")

    def test_import_byte_order(self):
        self.reject("crypto/bn/bn_lib.c", "ret, LITTLE, UNSIGNED);", "ret, BIG, UNSIGNED);")

    def test_import_zero_sign(self):
        self.reject("crypto/bn/bn_lib.c", "ret->top = 0;", "ret->top = 0; ret->neg = 0;")

    def test_serialization_width(self):
        self.reject("crypto/ec/ecp_nistp384.c", "memmove(&out[6], &in[42], 6);",
                    "memmove(&out[6], &in[42], 7);")

    def test_conversion_failure(self):
        self.reject("crypto/ec/ecp_nistp384.c", "if (num_bytes < 0)", "if (num_bytes > 0)")


if __name__ == "__main__":
    unittest.main()
