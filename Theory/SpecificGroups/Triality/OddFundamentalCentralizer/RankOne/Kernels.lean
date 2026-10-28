module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent
/-!
# Scalar tests for the actual triality quotient kernels

A faithful split SL₂ map can lose only scalar elements on quotienting the
elementary fixed group by its center. For the arm Frobenius diagonal,
commutation first reduces its split kernel to scalars; equality of the three
arm scalar involutions then makes that kernel trivial. These conditional
reductions are used with the explicit matrix scalar calculations.

Source: GLS3 §2.6, Proposition 2.6.2, and the fundamental-subgroup use in
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.RankOne
open Parabolics

lemma scalar_cases {F : Type*} [Field F] (a : SL(2, F))
    (ha : a ∈ Subgroup.center SL(2, F)) : a = 1 ∨ a = -1 := by
  obtain ⟨r, hr, hra⟩ := SpecialLinearGroup.mem_center_iff.mp ha
  simp only [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hra.symm
  · right
    apply Subtype.ext
    simpa [← Matrix.diagonal_neg] using hra.symm

lemma descendedHom_injective_of_scalar {F : Type*} [Field F]
    (P : Parameters) [CharP F P.prime] (f : SL(2, F) →* SplitGroup P)
    (hfixed : ∀ a, f a ∈ fixedSubgroup P) (hf : Function.Injective f)
    (hscalar : elementaryLift P f hfixed (-1) ∉ Subgroup.center (ElementaryGroup P)) :
    Function.Injective (descendedHom P f hfixed) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hz : elementaryLift P f hfixed a ∈ Subgroup.center (ElementaryGroup P) :=
    (toCarrier_eq_one P _).mp ha
  have hcentral : a ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hf
    simp only [map_mul]
    exact congrArg (elementaryInclusion P) ((Subgroup.mem_center_iff.mp hz)
      (elementaryLift P f hfixed b))
  rcases scalar_cases a hcentral with h | rfl
  · exact h
  · exact (hscalar hz).elim

lemma sl2Frobenius_neg_one (P : Parameters) : sl2Frobenius P (-1) = -1 := by
  ext i j
  change fieldFrobenius P (-((1 : Matrix (Fin 2) (Fin 2) (ExtensionField P)) i j)) =
    -((1 : Matrix (Fin 2) (Fin 2) (ExtensionField P)) i j)
  simp only [map_neg, Matrix.one_apply]
  split_ifs <;> simp only [map_one, map_zero]

lemma armsFixedEmbedding_injective_of_scalars {P : Parameters}
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)
    (h02 : D.hom 0 (-1) = D.hom 2 (-1))
    (h03 : D.hom 0 (-1) = D.hom 3 (-1)) :
    Function.Injective (D.armsFixedEmbedding C) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hprod : D.hom 0 a *
      (D.hom 2 (sl2Frobenius P a) * D.hom 3 (sl2Frobenius P (sl2Frobenius P a))) = 1 := by
    change D.hom 0 a * D.hom 2 (sl2Frobenius P a) *
      D.hom 3 (sl2Frobenius P (sl2Frobenius P a)) = 1 at ha
    simpa only [mul_assoc] using ha
  have hc : a ∈ Subgroup.center SL(2, ExtensionField P) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply D.injective 0
    simp only [map_mul]
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact ((D.commute C 0 2 (by decide) (by decide) (by decide) b _).mul_right
      (D.commute C 0 3 (by decide) (by decide) (by decide) b _)).inv_right.eq
  rcases scalar_cases a hc with h | rfl
  · exact h
  · simp only [sl2Frobenius_neg_one, ← h02, ← h03] at hprod
    have hsq : D.hom 0 (-1) * D.hom 0 (-1) = 1 := by
      rw [← map_mul]
      simp
    rw [hsq, mul_one] at hprod
    exact D.injective 0 (hprod.trans (map_one _).symm)
end Triality.Standard.OddFundamentalCentralizer.RankOne
