module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Solvable

/-!
# Nonsolvability of the concrete PSL₃(2)

The matrix group `Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)` is
not solvable. This intrinsic fact supplies the nonsolvable local model used
in Stellmacher's (8.6)(c) and (9.1), without importing that development.

We use the elementary-matrix commutator argument directly in Mathlib's model:
for distinct indices, `[t(row,mid), t(mid,col)] = t(row,col)`. The finitely many
matrix identities over `ZMod 2` are checked by kernel reduction. Their images
in SL modulo its center therefore belong to every term of the derived series,
by induction using `Subgroup.commutator_mem_commutator`. The image of `t(0,1)`
is nontrivial because this matrix does not commute with `t(1,2)` in SL.
Mathlib's `not_isSolvable_of_mem_derivedSeries` finishes the argument; neither
a simplicity theorem nor a different presentation of the group is needed.
-/

open scoped commutatorElement

private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

private def elementary (row col : Fin 3) : SL :=
  if different : row ≠ col then Matrix.SpecialLinearGroup.transvection different 1 else 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem elementary_commutator :
    ∀ row col mid : Fin 3, row ≠ col → row ≠ mid → mid ≠ col →
      ⁅elementary row mid, elementary mid col⁆ = elementary row col := by
  decide

private def project : SL →* PSL := QuotientGroup.mk' _

private theorem elementary_project_ne_one : project (elementary 0 1) ≠ 1 := by
  intro trivial
  have central : elementary 0 1 ∈ Subgroup.center SL :=
    (QuotientGroup.eq_one_iff _).mp trivial
  have commute := Subgroup.mem_center_iff.mp central (elementary 1 2)
  have different : elementary 1 2 * elementary 0 1 ≠ elementary 0 1 * elementary 1 2 := by
    decide
  exact different commute

private theorem elementary_mem_derived (stage : ℕ) :
    ∀ row col : Fin 3, row ≠ col → project (elementary row col) ∈ derivedSeries PSL stage := by
  induction stage with
  | zero => intros; trivial
  | succ stage ih =>
    intro row col different
    have exists_mid : ∀ row col : Fin 3, row ≠ col →
        ∃ mid : Fin 3, row ≠ mid ∧ mid ≠ col := by decide
    obtain ⟨mid, left, right⟩ := exists_mid row col different
    rw [← elementary_commutator row col mid different left right, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (ih row mid left) (ih mid col right)

/-- The concrete matrix projective special linear group PSL₃(2) is not solvable. -/
public theorem not_isSolvable_psl3_two :
    ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
  not_isSolvable_of_mem_derivedSeries elementary_project_ne_one
    (fun stage => elementary_mem_derived stage 0 1 (by decide))

/-- The determinant-one matrix group SL₃(2) is not solvable. -/
public theorem not_isSolvable_sl3_two :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  intro h
  let := h
  exact not_isSolvable_psl3_two inferInstance
