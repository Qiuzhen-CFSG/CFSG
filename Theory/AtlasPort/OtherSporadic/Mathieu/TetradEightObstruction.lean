/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradLocalNormal
public import Theory.AtlasPort.OtherSporadic.GroupTheory.AffineEightObstruction

/-!
# TetradEightObstruction

The tetrad pointwise stabilizer admits no faithful permutation action of degree eight.
Its sixteen-element translation module and faithful irreducible local action satisfy the
affine obstruction theorem, which transfers through the actual stabilizer equivalence.

Source: `Atlas/Mathieu/TetradEightObstruction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

theorem tetradAffine_no_faithful_eight (i : HexIndex) (X : Type*) [Finite X]
    [MulAction (TetradPointAffine i) X] [FaithfulSMul (TetradPointAffine i) X]
    (hx : Nat.card X = 8) : False := by
  apply Atlas.GroupTheory.affine_no_faithful_eight (hexZeroAffineAction i)
    (show Nat.card (Multiplicative (hexZeroCoordinate i)) = 16 from hexZeroCoordinate_card i) hx
  intro u v hu hv
  obtain ⟨g,hg⟩ := hexPointKernel_nonzero_transitive i u.toAdd v.toAdd hu hv
  exact ⟨g,hg⟩

theorem tetradPoint_no_faithful_eight (i : HexIndex) (X : Type*) [Finite X]
    [MulAction (TetradPointStabilizer i) X] [FaithfulSMul (TetradPointStabilizer i) X]
    (hx : Nat.card X = 8) : False := by
  let e := tetradPointStabilizerEquiv i
  let : MulAction (TetradPointAffine i) X := MulAction.compHom X e.toMonoidHom
  have : FaithfulSMul (TetradPointAffine i) X := ⟨fun {g h} he =>
    e.injective (eq_of_smul_eq_smul (α := X) he)⟩
  exact tetradAffine_no_faithful_eight i X hx

theorem tetradPoint_no_injective_perm_eight (i : HexIndex)
    (ρ : TetradPointStabilizer i →* Equiv.Perm (Fin 8)) : ¬ Function.Injective ρ := by
  intro hρ
  let : MulAction (TetradPointStabilizer i) (Fin 8) := MulAction.compHom (Fin 8) ρ
  have : FaithfulSMul (TetradPointStabilizer i) (Fin 8) := ⟨fun {g h} he =>
    hρ (Equiv.ext he)⟩
  exact tetradPoint_no_faithful_eight i (Fin 8) (by simp)

end Atlas.Codes
