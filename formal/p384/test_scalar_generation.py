#!/usr/bin/env python3
import json
import unittest

from generate_scalar import (HERE, SOURCE, UTIL, generate_constants, generate_doublings,
                             generate_output, generate_recode, source_snapshot)


class ScalarExtraction(unittest.TestCase):
    def setUp(self):
        self.source, self.util = SOURCE.read_text(), UTIL.read_text()
        self.snapshot = json.loads((HERE / "scalar-sources.json").read_text())["functions"]

    def test_current(self):
        self.assertEqual(source_snapshot(self.source, self.util), self.snapshot)
        self.assertEqual(generate_recode(self.util), (HERE / "P384/GeneratedBooth.lean").read_text())
        self.assertEqual(generate_constants(self.source), (HERE / "P384/GeneratedScalarConstants.lean").read_text())
        self.assertEqual(generate_doublings(self.source), (HERE / "P384/GeneratedGeneratorWitness.lean").read_text())
        self.assertEqual(generate_output(self.source), (HERE / "P384/GeneratedScalarOutput.lean").read_text())

    def test_recode_expression(self):
        changed = self.util.replace("d = (d >> 1) + (d & 1);", "d = (d >> 1);", 1)
        self.assertNotEqual(generate_recode(changed), generate_recode(self.util))

    def test_recode_extra_statement(self):
        with self.assertRaises(ValueError):
            generate_recode(self.util.replace("*digit = d;", "*digit = d; d = 0;", 1))

    def test_recode_declaration(self):
        with self.assertRaises(ValueError):
            generate_recode(self.util.replace("unsigned char s, d;", "unsigned int s, d;", 1))

    def test_undefined_shift(self):
        with self.assertRaises(ValueError):
            generate_recode(self.util.replace("d >> 1", "d >> 32", 1))

    def test_unsupported_expression(self):
        with self.assertRaises(ValueError):
            generate_recode(self.util.replace("d >> 1", "d * 2", 1))

    def test_batch_schedule_snapshot(self):
        changed = self.source.replace("num_points ? 380 : 98", "num_points ? 379 : 98", 1)
        self.assertNotEqual(source_snapshot(changed, self.util), self.snapshot)

    def test_comb_boundary_snapshot(self):
        changed = self.source.replace("if (i < 95)", "if (i < 94)", 1)
        self.assertNotEqual(source_snapshot(changed, self.util), self.snapshot)

    def test_skip_snapshot(self):
        changed = self.source.replace("skip = 1;", "skip = 0;", 1)
        self.assertNotEqual(source_snapshot(changed, self.util), self.snapshot)

    def test_select_snapshot(self):
        changed = self.source.replace("mask |= mask >> 4;", "mask |= mask >> 3;", 1)
        self.assertNotEqual(source_snapshot(changed, self.util), self.snapshot)

    def test_bit_guard_snapshot(self):
        changed = self.source.replace("i < 0 || i >= 384", "i < 0 || i >= 383", 1)
        self.assertNotEqual(source_snapshot(changed, self.util), self.snapshot)

    def test_curve_byte_width(self):
        changed = self.source.replace("{ 0xB3, 0x31", "{ 0x1B3, 0x31", 1)
        with self.assertRaises(ValueError):
            generate_constants(changed)

    def test_curve_dimensions(self):
        with self.assertRaises(ValueError):
            generate_constants(self.source.replace("nistp384_curve_params[5]", "nistp384_curve_params[6]", 1))

    def test_table_constant(self):
        self.assertIn("0x00545e3872760ab7", self.source)
        changed = self.source.replace("0x00545e3872760ab7", "0x00545e3872760ab8", 1)
        self.assertNotEqual(generate_constants(changed), generate_constants(self.source))

    def test_output_zero_initialization(self):
        with self.assertRaises(ValueError):
            generate_output(self.source.replace("widefelem wide_y = { 0 };", "widefelem wide_y;", 1))

    def test_output_copy_bound(self):
        with self.assertRaises(ValueError):
            generate_output(self.source.replace("i < NLIMBS; i++)\n        wide_y[i]", "i < NLIMBS - 1; i++)\n        wide_y[i]", 1))

    def test_output_reduction(self):
        with self.assertRaises(ValueError):
            generate_output(self.source.replace("felem_reduce(y_out, wide_y);", "felem_assign(y_out, nq[1]);", 1))

    def test_output_extra_write(self):
        with self.assertRaises(ValueError):
            generate_output(self.source.replace("felem_reduce(y_out, wide_y);", "wide_y[7] = 1; felem_reduce(y_out, wide_y);", 1))

    def test_output_limb_count(self):
        with self.assertRaises(ValueError):
            generate_output(self.source.replace("#define NLIMBS 7", "#define NLIMBS 6", 1))


if __name__ == "__main__":
    unittest.main()
