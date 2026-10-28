module

public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Comparison
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ternary elementary isometries in the full commutator subgroup

For the form `xy + z²`, the full isometry `(x,y,z) ↦ (-x,-y,z)`
inverts the image of every SL₂ transvection. When two is nonzero, the
transvection with parameter `a` is therefore the commutator of this isometry
with the root at parameter `-a/2`. Elementary generation and the proved
rank-one comparison place the entire elementary ternary carrier in the full
orthogonal commutator subgroup, including over F₃.

The consumer in `RankTwoCubic` extends this carrier to the four-dimensional
minus form. This supplies the smallest complementary cubic needed in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39, using the carrier conventions of GLS3 §2.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
open scoped commutatorElement
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer.RankTwoCubic
variable {F : Type*} [Field F]

/-- The full isometry group of the ternary form. -/
abbrev TernaryO := quadraticIsometrySubgroup (formB 1 F)

private def flipLinear : VectorB 1 F ≃ₗ[F] VectorB 1 F where
  toFun x := (-x.1, x.2)
  invFun x := (-x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [add_comm]
  map_smul' a x := by simp

private def flip : TernaryO (F := F) :=
  ⟨flipLinear, (mem_quadraticIsometrySubgroup _ _).mpr (by
    intro x
    simp [flipLinear, formB_apply, formD_apply])⟩

private theorem flip_conj_transvection {i j : Fin 2} (hij : i ≠ j) (a : F) :
    flip * RankOneComparison.toOrthogonal (SpecialLinearGroup.transvection hij a) * flip⁻¹ =
      RankOneComparison.toOrthogonal (SpecialLinearGroup.transvection hij (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · apply Prod.ext
    · ext k; rcases k with k|k <;> fin_cases k
      all_goals
        simp [flip, flipLinear, RankOneComparison.toOrthogonal, RankOneComparison.onB,
          RankOneComparison.coordinates, RankOneComparison.kernelAction, RankOneComparison.kernelMap,
          SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
          Fin.sum_univ_two] <;> ring
    · simp [flip, flipLinear, RankOneComparison.toOrthogonal, RankOneComparison.onB,
        RankOneComparison.coordinates, RankOneComparison.kernelAction, RankOneComparison.kernelMap,
        SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two]
  · apply Prod.ext
    · ext k; rcases k with k|k <;> fin_cases k
      all_goals
        simp [flip, flipLinear, RankOneComparison.toOrthogonal, RankOneComparison.onB,
          RankOneComparison.coordinates, RankOneComparison.kernelAction, RankOneComparison.kernelMap,
          SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
          Fin.sum_univ_two] <;> ring
    · simp [flip, flipLinear, RankOneComparison.toOrthogonal, RankOneComparison.onB,
        RankOneComparison.coordinates, RankOneComparison.kernelAction, RankOneComparison.kernelMap,
        SpecialLinearGroup.transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two]
  · exact False.elim (hij rfl)

private theorem transvection_mem_derived (h2 : (2 : F) ≠ 0)
    {i j : Fin 2} (hij : i ≠ j) (a : F) :
    RankOneComparison.toOrthogonal (SpecialLinearGroup.transvection hij a) ∈
      commutator (TernaryO (F := F)) := by
  have he : ⁅(flip (F := F)), RankOneComparison.toOrthogonal
      (SpecialLinearGroup.transvection hij (-a / 2))⁆ =
      RankOneComparison.toOrthogonal (SpecialLinearGroup.transvection hij a) := by
    rw [commutatorElement_def, flip_conj_transvection, ← map_inv,
      SpecialLinearGroup.transvection_inv, ← map_mul, ← SpecialLinearGroup.transvection_add]
    congr 2
    field_simp [h2]
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The rank-one SL₂ image lies in the full ternary commutator subgroup. -/
theorem sl_mem_derived (h2 : (2 : F) ≠ 0) (g : RankOneComparison.SL (F := F)) :
    RankOneComparison.toOrthogonal g ∈ commutator (TernaryO (F := F)) := by
  apply Atlas.sl_elementary_induction
    (fun g => RankOneComparison.toOrthogonal g ∈ commutator (TernaryO (F := F)))
  · intro i j hij a
    exact transvection_mem_derived h2 hij a
  · intro a b ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb

/-- Inclusion of the actual elementary ternary carrier in the full derived group. -/
def ternaryElementaryDerived (h2 : (2 : F) ≠ 0) :
    OmegaOdd 1 F →* commutator (TernaryO (F := F)) :=
  (elementarySubgroup (formB 1 F)).subtype.codRestrict _ (by
    intro g
    obtain ⟨a, rfl⟩ := RankOneComparison.toElementary_surjective g
    exact sl_mem_derived h2 a)

/-- The comparison retains the original isometries, so it is injective. -/
theorem ternaryElementaryDerived_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (ternaryElementaryDerived h2) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : commutator (TernaryO (F := F)) => x.val) h)

end ClassicalOrthogonal.Fundamental.MinusCentralizer.RankTwoCubic
