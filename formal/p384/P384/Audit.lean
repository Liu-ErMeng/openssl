import P384.Words
import P384.Points
import P384.Counterexamples
import P384.GeneratedMachine
import P384.MachineInversion
import P384.ZeroRefinement
import P384.InterfaceValues
import P384.Contract
import P384.FieldInterfaces
import P384.CheckedFieldInterfaces
import P384.ScalarPrecompute
import P384.ScalarNegation
import P384.ScalarTable
import P384.JacobianScalar
import P384.ScalarCounterexample
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`P384).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "{name}: unapproved axiom {axiomName}"
      | _ => pure ()
  unless count ≥ 40 do
    throwError "Incomplete imports: only {count} theorems audited"
  logInfo m!"Axiom audit: {count} theorems; only propext, Classical.choice, Quot.sound allowed"
