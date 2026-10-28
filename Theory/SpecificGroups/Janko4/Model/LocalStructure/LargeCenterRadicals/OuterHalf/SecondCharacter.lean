module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.InnerHalves
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Core

/-! The intrinsic second-centralizer residual is exactly the pointwise stabilizer
of the two marked star coordinates. This retains the actual max1 conjugation
map and the native M22 inclusion. Source: Kleidman--Wilson (1988), p.487. -/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.InvolutionCentralizers.Second
open Janko4.Cardinality.QuotientCount.Image
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  StarGroup markedStarEquiv pairMarking

private theorem native_inner_iff (p : MathieuCode.m22PairStabilizer) :
    MathieuCode.m22PairStabilizerEquivAut p ∈ MulAut.innerSubgroup M22 ↔
      (p.val.val 0 = 0 ∧ p.val.val 9 = 9) := by
  constructor
  · rintro ⟨g, hg⟩
    have he : MathieuCode.m22ToPairStabilizer g = p :=
      MathieuCode.m22PairStabilizerEquivAut.injective
        ((MathieuCode.m22PairStabilizerEquivAut_inner g).trans hg)
    rw [← he]
    exact ⟨MathieuCode.m22Embedding_fixed_zero g, MathieuCode.m22Embedding_fixed_nine g⟩
  · intro hp
    have hr : p.val ∈ MathieuCode.m22Embedding.range := by
      rw [MathieuCode.m22Embedding_range]
      exact hp
    obtain ⟨g, hg⟩ := hr
    have he : MathieuCode.m22ToPairStabilizer g = p := Subtype.ext hg
    exact ⟨g, (MathieuCode.m22PairStabilizerEquivAut_inner g).symm.trans
      (congrArg MathieuCode.m22PairStabilizerEquivAut he)⟩

/-- The full residual character of the second centralizer is pointwise pair fixation. -/
theorem innerRelated_second_iff_star (g : localCentralizer) :
    InnerRelated (seed : Model) (g.val : Model) ↔
      ((starHom g.val).val 0 = 0 ∧ (starHom g.val).val 1 = 1) := by
  have hm : InnerRelated (seed : Model) (g.val : Model) ↔
      ambientEquivLocal.symm g ∈ solvableResidual ambientCentralizer := by
    change ambientCentralizer.subtype (ambientEquivLocal.symm g) ∈
      (solvableResidual ambientCentralizer).map ambientCentralizer.subtype ↔ _
    exact mem_map_iff_mem ambientCentralizer.subtype_injective
  rw [hm, ← second_innerHalf_eq_residual]
  change toAutM22 (ambientEquivLocal (ambientEquivLocal.symm g)) ∈ MulAut.innerSubgroup M22 ↔ _
  rw [ambientEquivLocal.apply_symm_apply]
  change MathieuCode.m22PairStabilizerEquivAut (starPairEquivNative (toStarPair g)) ∈ MulAut.innerSubgroup M22 ↔ _
  rw [native_inner_iff]
  have h0 := markedStarEquiv_apply (starHom g.val) 0
  have h1 := markedStarEquiv_apply (starHom g.val) 1
  rw [pairMarking_zero] at h0
  rw [pairMarking_one] at h1
  change ((markedStarEquiv (starHom g.val)).val 0 = 0 ∧
    (markedStarEquiv (starHom g.val)).val 9 = 9) ↔ _
  have h0' : (markedStarEquiv (starHom g.val)).val 0 = 0 ↔ (starHom g.val).val 0 = 0 := by
    calc
      _ ↔ pairMarking ((starHom g.val).val 0) = pairMarking 0 := by rw [h0, pairMarking_zero]
      _ ↔ _ := pairMarking.injective.eq_iff
  have h1' : (markedStarEquiv (starHom g.val)).val 9 = 9 ↔ (starHom g.val).val 1 = 1 := by
    calc
      _ ↔ pairMarking ((starHom g.val).val 1) = pairMarking 1 := by rw [h1, pairMarking_one]
      _ ↔ _ := pairMarking.injective.eq_iff
  exact and_congr h0' h1'

open Janko4.Cardinality Janko4.Simplicity.Max1Fusion.KernelOrbits

private theorem star_image (g : localCentralizer) (n : ℕ) (hn : n < 2048)
    (he : (g.val : Model) * ((maskValue matrixA_mul_self matrixB_pow_four 28).val : Model) *
      (g.val : Model)⁻¹ = ((maskValue matrixA_mul_self matrixB_pow_four n).val : Model)) :
    pairLabel ((starHom g.val).val 0) ((starHom g.val).val 2) = n := by
  have ha := starHom_pair g.val 0 2
  apply congrArg Fin.val (Janko4.Max1RelativeRigidity.maskValue_injective
    (a₁ := ⟨_, pairLabel_lt _ _⟩) (a₂ := ⟨n, hn⟩) ?_)
  change maskValue _ _ (pairLabel ((starHom g.val).val 0) ((starHom g.val).val 2)) = maskValue _ _ n
  rw [← ha]
  apply Subtype.ext
  apply Subtype.ext
  simpa only [QuotientCount.action_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    show pairLabel 0 2 = 28 from rfl] using he

private theorem star_zero_or_one (g : localCentralizer) :
    (starHom g.val).val 0 = 0 ∨ (starHom g.val).val 0 = 1 := by
  have h := MulAction.mem_stabilizer_finset'.mp (toStarPair g).property
    (show (0 : Fin 24) ∈ starPair by simp [starPair])
  change (starHom g.val).val 0 ∈ starPair at h
  simpa only [starPair, Finset.mem_insert, Finset.mem_singleton] using h

private theorem star_one_or_zero (g : localCentralizer) :
    (starHom g.val).val 1 = 0 ∨ (starHom g.val).val 1 = 1 := by
  have h := MulAction.mem_stabilizer_finset'.mp (toStarPair g).property
    (show (1 : Fin 24) ∈ starPair by simp [starPair])
  change (starHom g.val).val 1 ∈ starPair at h
  simpa only [starPair, Finset.mem_insert, Finset.mem_singleton] using h

/-- The actual kernel-pair image 180 forces the inner half. -/
theorem second_inner_of_pair_image180 (g : localCentralizer)
    (he : (g.val : Model) * ((maskValue matrixA_mul_self matrixB_pow_four 28).val : Model) *
      (g.val : Model)⁻¹ = ((maskValue matrixA_mul_self matrixB_pow_four 180).val : Model)) :
    InnerRelated (seed : Model) (g.val : Model) := by
  have hl := star_image g 180 (by decide) he
  have hex : ∀ j : Fin 24, pairLabel 1 j ≠ 180 := by decide +kernel
  have h0 : (starHom g.val).val 0 = 0 := (star_zero_or_one g).resolve_right
    (fun h => hex _ (h ▸ hl))
  have h1 : (starHom g.val).val 1 = 1 := (star_one_or_zero g).resolve_left (fun h =>
    (show (1 : Fin 24) ≠ 0 by decide) ((starHom g.val).val.injective (h.trans h0.symm)))
  exact (innerRelated_second_iff_star g).mpr ⟨h0, h1⟩

/-- Either of the two displayed pair images forces the outer half. -/
theorem second_not_inner_of_pair_image (g : localCentralizer) (n : ℕ)
    (hn : n = 1059 ∨ n = 29)
    (he : (g.val : Model) * ((maskValue matrixA_mul_self matrixB_pow_four 28).val : Model) *
      (g.val : Model)⁻¹ = ((maskValue matrixA_mul_self matrixB_pow_four n).val : Model)) :
    ¬ InnerRelated (seed : Model) (g.val : Model) := by
  have hb : n < 2048 := by rcases hn with rfl | rfl <;> decide
  have hl := star_image g n hb he
  intro hi
  rw [(innerRelated_second_iff_star g).mp hi |>.1] at hl
  have hex : ∀ j : Fin 24, pairLabel 0 j ≠ 1059 ∧ pairLabel 0 j ≠ 29 := by decide +kernel
  rcases hn with rfl | rfl
  · exact (hex _).1 hl
  · exact (hex _).2 hl

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
