#!/usr/bin/env python3
import unittest

from generate_bn_bits import SOURCE, generate
from generate import body
from check_interfaces import ROOT, check


class BNWordBitsExtraction(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text()

    def reject(self, old, new):
        self.assertIn(old, self.source)
        with self.assertRaises(ValueError):
            generate(self.source.replace(old, new, 1))

    def test_shift_stage(self):
        self.reject("x = l >> 32;", "x = l >> 31;")

    def test_counter_increment(self):
        self.reject("bits += 16 & mask;", "bits += 15 & mask;")

    def test_high_bit_mask(self):
        self.reject("mask >> (BN_BITS2 - 1)", "mask >> (BN_BITS2 - 2)")

    def test_missing_limb_update(self):
        self.reject("l ^= (x ^ l) & mask;", "")

    def test_early_return(self):
        fragment = body(self.source, "BN_num_bits_word")
        with self.assertRaises(ValueError):
            generate(self.source.replace(fragment, "return 0;" + fragment, 1))

    def test_undefined_shift(self):
        self.reject("x = l >> 32;", "x = l >> 64;")

    def test_word_selection(self):
        self.reject("#if BN_BITS2 > 32", "#if BN_BITS2 > 64")

    def test_signed_counter_type(self):
        self.reject("int bits = (l != 0);", "unsigned int bits = (l != 0);")

    def test_ct_helper_snapshot(self):
        path = "include/internal/constant_time.h"
        source = (ROOT / path).read_text()
        old = "return constant_time_msb(~a & (a - 1));"
        self.assertIn(old, source)
        with self.assertRaises(ValueError):
            check({path: source.replace(old, "return constant_time_msb(a & (a - 1));", 1)})

    def test_release_flag_macro_snapshot(self):
        path = "crypto/bn/bn_local.h"
        source = (ROOT / path).read_text()
        old = "#define BN_FLG_FIXED_TOP 0\n"
        self.assertIn(old, source)
        with self.assertRaises(ValueError):
            check({path: source.replace(old, "#define BN_FLG_FIXED_TOP 0x10000\n", 1)})


if __name__ == "__main__":
    unittest.main()
