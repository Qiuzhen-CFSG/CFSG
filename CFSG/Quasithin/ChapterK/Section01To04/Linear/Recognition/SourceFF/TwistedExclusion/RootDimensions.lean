module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy

/-!
# Every inner involution has the Hermitian root displacement

Sylow conjugacy puts an involution of the actual inner image into the
unitriangular image, where the covering map is injective. The explicit
SL₃ root conjugacy then gives its displacement on the original Hermitian
space. Thus the strict quadratic bound has no remaining root-dimension
premise.

Source: Aschbacher–Smith, H.4.4(2) and K.3.2.4, printed pp.381,455–456.
-/

public section
noncomputable section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender Subgroup
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
open CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
  (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

include hM in
/-- The H.4.4 root dimension holds for every actual inner involution. -/
theorem innerRootDimensions : InnerRootDimensions n M := by
  intro i hi hi2
  let j : innerActor n M := ⟨i, hi⟩
  have hj2 : orderOf j = 2 := by
    rw [← orderOf_injective (innerActor n M).subtype Subtype.val_injective]
    exact hi2
  obtain ⟨y, hy⟩ := (innerSylow n M hM).exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa only [pow_one] using hj2)
  have hyU : (y : innerActor n M).val ∈ unipotentActor n M hM := by
    rw [← innerSylow_map n M hM]
    exact mem_map_of_mem (innerActor n M).subtype y.property
  obtain ⟨u, hu⟩ := hyU
  have hiy : IsConj i (unipotentToOvergroup n M hM u) := by
    exact hu ▸ (innerActor n M).subtype.map_isConj hy
  obtain ⟨c, hc⟩ := isConj_iff.mp hiy
  have hiPow : i ^ 2 = 1 := by simpa only [hi2] using pow_orderOf_eq_one i
  have hu2 : u ^ 2 = 1 := by
    apply unipotentToOvergroup_injective n M hM
    rw [map_pow, map_one, ← hc]
    change (MulAut.conj c i) ^ 2 = 1
    rw [← map_pow, hiPow, map_one]
  have hun : u ≠ 1 := by
    intro hu1
    have hi1 : i = 1 := by
      apply (MulAut.conj c).injective
      have huImage : unipotentToOvergroup n M hM u = 1 :=
        (congrArg (unipotentToOvergroup n M hM) hu1).trans
          (map_one (unipotentToOvergroup n M hM))
      exact hc.trans (huImage.trans (map_one (MulAut.conj c)).symm)
    simp [hi1] at hi2
  have hc := Matrix.PSL3.EvenInnerCentralizers.specialLinear_isConj_root (E n) u hun hu2
  have hc' : IsConj (unipotentToOvergroup n M hM u)
      (coverToOvergroup n M hM (root n)) :=
    (coverToOvergroup n M hM).map_isConj hc
  obtain ⟨g, hg⟩ := isConj_iff.mp (hiy.trans hc')
  have hr := CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.overgroup_root_fixedCodim
    n M (sourceOvergroup_contains_image n M hM ⟨root n, rfl⟩)
  change fixedCodim (overgroupAction n M) (zpowers (coverToOvergroup n M hM (root n))) = _ at hr
  rw [← hg, fixedCodim_zpowers_conj] at hr
  exact hr

include hM in
/-- The genuine tensor overgroup cannot have an FF module. -/
theorem not_isFFModule : ¬ IsFFModule (overgroupAction n M) := by
  intro hff
  have hu := (isFFModule_iff_quadraticRatio_le_one _).mp hff
  have hl := quadraticRatio_gt_two_of_inner_source_dimensions n M hM
    (innerRootDimensions n M hM)
  exact (not_le_of_gt hl) (hu.trans (by norm_num))

end CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
