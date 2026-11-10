#!/usr/bin/env python3
import unittest

from generate import SOURCE, body, generate, generate_zero


class ExtractionBoundary(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text()
        self.fragment = body(self.source, "felem_reduce_ref")

    def reject(self, fragment):
        source = self.source.replace(self.fragment, fragment, 1)
        for machine in (False, True):
            with self.subTest(machine=machine), self.assertRaises(ValueError):
                generate(source, machine=machine)

    def test_reject_unmodeled_output_write(self):
        self.reject(self.fragment + "\nmemset(out, 0, sizeof(felem));\n")

    def test_reject_unmodeled_early_return(self):
        self.reject(self.fragment.replace("    memcpy(acc, in,", "    if (in[0] == 0) return;\n    memcpy(acc, in,", 1))

    def test_reject_changed_input_copy_size(self):
        self.reject(self.fragment.replace("sizeof(widelimb) * 9", "sizeof(widelimb) * 8", 1))

    def test_reject_changed_output_loop(self):
        self.reject(self.fragment.replace("i < NLIMBS", "i < NLIMBS - 1", 1))

    def test_reject_changed_limb_count(self):
        source = self.source.replace("#define NLIMBS 7", "#define NLIMBS 8", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_unmodeled_narrowing_cast(self):
        self.reject(self.fragment.replace("in[12] >> 32", "(limb)in[12] >> 32", 1))

    def test_reject_undefined_shift(self):
        self.reject(self.fragment.replace("in[12] >> 32", "in[12] >> 128", 1))

    def test_reject_missing_widening_cast(self):
        source = self.source.replace("((uint128_t)in1[0]) * in2[0]", "in1[0] * in2[0]", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_unmodeled_product_write(self):
        fragment = body(self.source, "felem_mul_ref")
        source = self.source.replace(fragment, fragment + "\nmemset(out, 0, sizeof(widefelem));\n", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_changed_square_helper(self):
        source = self.source.replace("out[i] = in[i] * scalar;", "out[i] = in[i] * (scalar + 1);", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_unmodeled_inverse_write(self):
        fragment = body(self.source, "felem_inv")
        source = self.source.replace(fragment, fragment + "\nmemset(out, 0, sizeof(felem));\n", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_changed_reduce_wrapper(self):
        fragment = body(self.source, "felem_mul_reduce_ref")
        source = self.source.replace(fragment, fragment + "\nout[0] = 0;\n", 1)
        with self.assertRaises(ValueError):
            generate(source)

    def test_reject_changed_zero_return(self):
        source = self.source.replace("return (zero | p384);", "return 0;", 1)
        with self.assertRaises(ValueError):
            generate_zero(source)

    def test_reject_zero_mask_overwrite(self):
        source = self.source.replace("return (zero | p384);", "zero = 0; p384 = 0; return (zero | p384);", 1)
        with self.assertRaises(ValueError):
            generate_zero(source)


if __name__ == "__main__":
    unittest.main()
