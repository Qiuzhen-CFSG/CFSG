module

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Authors: ATLAS contributors.
-/

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic

/-!
# Support for the exceptional projective linear comparisons

The determinant kernel counts SL; its scalar center is the kernel of a power
map on the cyclic group of field units. These two quotient counts give the
order identity needed by the faithful-action comparisons. Entrywise field
transport descends through the center to the projective quotient.

The center count, projective-point count, and field transport are adapted from
Gerald Höhn and ATLAS contributors, `Atlas/LinearGroups/ProjectiveSpecialLinear.lean`,
`ProjectiveGeneralLinear.lean`, and `PSLFieldTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. ATLAS Research and Attribution
License 1.0 applies; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
Changes: only the required declarations are retained, and order computations
use the determinant kernel directly instead of PGL.
-/

namespace Atlas
open scoped MatrixGroups LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K]

public theorem card_projectiveSpace (n : ℕ) [Finite F] :
    Nat.card (ℙ F (Fin n → F)) = (Nat.card F ^ n - 1) / (Nat.card F - 1) := by
  simpa [Nat.card_fun] using Projectivization.card'' F (Fin n → F)

@[expose] public def fieldEquivSL (n : ℕ) (e : F ≃+* K) : SL(n,F) ≃* SL(n,K) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply _
  right_inv g := by ext i j; exact e.apply_symm_apply _
  map_mul' g h := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul g h

public def fieldEquivPSL (n : ℕ) (e : F ≃+* K) : PSL(n,F) ≃* PSL(n,K) :=
  QuotientGroup.congr _ _ (fieldEquivSL n e) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr (fieldEquivSL n e) ⟨y, hy⟩).property
    · intro hx
      exact ⟨(fieldEquivSL n e).symm x,
        (Subgroup.centerCongr (fieldEquivSL n e).symm ⟨x, hx⟩).property,
        (fieldEquivSL n e).apply_symm_apply x⟩)

namespace ExceptionalSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

public theorem card_sl_center [Nonempty ι] [Finite F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup ι F)) =
      Nat.gcd (Fintype.card ι) (Nat.card F - 1) := by
  let e := (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := F) (Classical.arbitrary ι)).trans (MulEquiv.subgroupCongr rootsOfUnity_eq_ker)
  rw [Nat.card_congr e.toEquiv, IsCyclic.card_powMonoidHom_ker,
    Nat.card_units, Nat.gcd_comm]

private def slEquivDetKer :
    Matrix.SpecialLinearGroup ι F ≃
      (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun A := ⟨A.1.val, congrArg Units.val A.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

/-- A fraction-free order formula, suited to concrete finite-field checks. -/
public theorem card_psl_mul (n : ℕ) [NeZero n] [Finite F] :
    Nat.card PSL(n,F) * Nat.gcd n (Nat.card F - 1) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  classical
  let := Fintype.ofFinite F
  have h := (Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
    Subgroup.card_top, ← Nat.card_congr (slEquivDetKer (ι := Fin n) (F := F)),
    Nat.card_units] at h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SL(n,F))), card_sl_center, Fintype.card_fin] at h
  convert h using 1
  simpa only [Nat.card_eq_fintype_card] using (Matrix.card_GL_field (𝔽 := F) n).symm

end ExceptionalSupport
end Atlas
