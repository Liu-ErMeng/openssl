#!/usr/bin/env bash
set -euo pipefail
proof_dir=$(cd -- "$(dirname -- "$0")" && pwd)
lean_root=${LEAN_P384_ROOT:-/usr1/lem/tmp/lean4-p384}
export PATH="$lean_root/lean-4.19.0-linux/bin:$PATH"
mathlib_dir=${MATHLIB_DIR:-$lean_root/mathlib4}
python3 "$proof_dir/generate.py" --check
python3 "$proof_dir/generate_primality.py" --check
python3 "$proof_dir/check_interfaces.py"
python3 "$proof_dir/generate_contract.py" --check
python3 "$proof_dir/generate_bn_bits.py" --check
python3 "$proof_dir/generate_scalar.py" --check
mkdir -p "$proof_dir/.build/P384"
cd "$mathlib_dir"
dependency_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_dir/.build:$dependency_path"
modules=(Basic Words Pratt Prime Generated Field Machine WordSemantics Representation Bytes BNBytes Serialization BNImport BNExport ByteMemory SerializationMemory InterfaceValues Counterexamples Reduction GeneratedMachine GeneratedProducts ProductRefinement GeneratedZero ZeroRefinement Inversion MachineInversion Points SignedWords Carry GeneratedContract ContractCompare BitSlices ContractArithmetic ContractFirst ContractCarry ContractConditions ContractGates ContractSubtract Contract FieldInterfaces BitWidth GeneratedBNWordBits BNWordBits BNNormalize ConstantTime32 BNNumBits BNLength BNToFelem CheckedFieldInterfaces ScalarBits GeneratedBooth Booth Comb Selection ScalarWindows BatchSchedule ScalarMul ScalarPrecompute ScalarNegation GeneratedScalarOutput ScalarOutput CurveGroup JacobianBatch JacobianPrecompute GeneratedScalarConstants ScalarCurve GeneratedGeneratorWitness ScalarTable JacobianScalar ScalarCounterexample Audit)
if (( $# )); then modules=("$@"); fi
for module in "${modules[@]}"; do
    printf 'Checking %s\n' "$module"
    lean -s 65536 --root="$proof_dir" -o "$proof_dir/.build/P384/$module.olean" "$proof_dir/P384/$module.lean"
done
if (( $# == 0 )); then
    lean --root="$proof_dir/../.." "$proof_dir/../../ecp_nistp384.lean"
fi
