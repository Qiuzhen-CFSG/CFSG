module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/SingularPoints.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.SingularOctonions
public import Theory.AtlasPort.LinearAlgebra.ProjectiveConeCount

@[expose] public section

/-! Actual singular one-dimensional subspaces in the trace-zero split octonions. -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.G2
open Atlas.SplitOctonion
variable (F : Type*) [Field F]

/-- Intrinsic projective points with trace-zero, norm-zero representative. -/
abbrev SingularPoints :=
  {p : ℙ F (Carrier F) // trace p.rep = 0 ∧ SplitOctonion.norm p.rep = 0}

theorem singular_smul_iff (a : Fˣ) (x : Carrier F) :
    (trace (a • x) = 0 ∧ SplitOctonion.norm (a • x) = 0) ↔
      (trace x = 0 ∧ SplitOctonion.norm x = 0) := by
  have ht : trace (a • x) = a.val * trace x := by
    simp [trace, Units.smul_def, Pi.smul_apply, smul_eq_mul, _root_.mul_add]
  have hn : SplitOctonion.norm (a • x) = a.val ^ 2 * SplitOctonion.norm x := by
    simp only [SplitOctonion.norm, Units.smul_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [ht, hn]
  simp [a.ne_zero]

/-- A nonzero singular octonion determines its actual one-dimensional span. -/
def singularPointMk (x : Carrier F) (hx : x ≠ 0)
    (ht : trace x = 0) (hn : SplitOctonion.norm x = 0) : SingularPoints F :=
  Atlas.LinearAlgebra.conePointMk
    (fun x : Carrier F => trace x = 0 ∧ SplitOctonion.norm x = 0)
    (singular_smul_iff F) ⟨x,hx,ht,hn⟩

theorem singularPointMk_rep (p : SingularPoints F) :
    singularPointMk F p.val.rep p.val.rep_nonzero p.prop.1 p.prop.2 = p :=
  Subtype.ext (Projectivization.mk_rep p.val)

/-- Reordering the same three intrinsic conditions changes no vector. -/
def nonzeroConeEquivSingularOctonions :
    Atlas.LinearAlgebra.NonzeroCone (fun x : Carrier F =>
      trace x = 0 ∧ SplitOctonion.norm x = 0) ≃ NonzeroSingularOctonions F where
  toFun x := ⟨⟨x.val,x.prop.2⟩,x.prop.1⟩
  invFun x := ⟨x.val.val,x.prop,x.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Nonzero singular vectors are projective representatives times nonzero scalars. -/
def nonzeroSingularEquivPointsUnits :
    NonzeroSingularOctonions F ≃ SingularPoints F × Fˣ :=
  (nonzeroConeEquivSingularOctonions F).symm.trans
    (Atlas.LinearAlgebra.nonzeroConeEquivPointsUnits _ (singular_smul_iff F))

theorem card_singularPoints [Finite F] :
    Nat.card (SingularPoints F) = (Nat.card F ^ 6 - 1) / (Nat.card F - 1) := by
  change Nat.card (Atlas.LinearAlgebra.ConePoints (F := F)
    (fun x : Carrier F => trace x = 0 ∧ SplitOctonion.norm x = 0)) = _
  rw [Atlas.LinearAlgebra.card_conePoints _ (singular_smul_iff F),
    Nat.card_congr (nonzeroConeEquivSingularOctonions F), card_nonzeroSingularOctonions]

theorem card_singularPoints_sum [Finite F] :
    Nat.card (SingularPoints F) = ∑ i ∈ Finset.range 6, Nat.card F ^ i := by
  rw [card_singularPoints]
  exact (Nat.geomSum_eq (Finite.one_lt_card (α := F)) 6).symm

end Atlas.G2
