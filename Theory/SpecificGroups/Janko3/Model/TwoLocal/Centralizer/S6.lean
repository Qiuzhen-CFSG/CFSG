module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S5

import Mathlib.Tactic.FinCases

/-!
# Generators at level 6 of the S chain

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal.CentralizerCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

@[expose] public def S6Gen : Fin 0 → Equiv.Perm (Fin 6156) := Fin.elim0
@[expose] public def S6Inv : Fin 0 → Fin 0 := Fin.elim0
public theorem S6Inv_spec (i : Fin 0) :
    S6Gen (S6Inv i) = (S6Gen i)⁻¹ := Fin.elim0 i

@[expose] public def S6H : Subgroup (Equiv.Perm (Fin 6156)) :=
  wordSubgroup S6Gen S6Inv S6Inv_spec

public theorem S6H_le : S6H ≤ S5H := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  exact Fin.elim0 i

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
