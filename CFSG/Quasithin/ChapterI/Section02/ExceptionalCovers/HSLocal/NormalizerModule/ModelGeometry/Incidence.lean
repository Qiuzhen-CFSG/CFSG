module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Core
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Incidence.Concrete
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry.Action
public import Theory.GroupTheory.ElementaryEightParabolicRecognition

/-!
# Normal generation and marked quotient fusion for the HS normalizer

The concrete inclusions use the literal pair kernel and alternating preimage.
The cyclic generator squares to e0. The full normalizer automorphism action
carries this square to every nonidentity element of the elementary eight,
so its normal closure contains square roots of all eight elements. The
square-map kernel then proves that this normal closure is the entire C₄³
core. The explicit two-central involution s0 remains an involution in the
quotient; the established quotient fusion theorem applies to that image.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423;
GLS3 Table 5.3m. The parent geometry assembly identifies P, T and W with the
source two-core, two-residual and center; those identifications are not
assumed in these incidence proofs.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open Theory.GroupTheory.DoubleCoverCentralizer
set_option maxRecDepth 20000

private theorem cyclicGenerator_mem_W : cyclicGenerator.val.val ∈ W := by
  refine ⟨cyclicGenerator.val, ⟨cyclicGenerator, ?_, rfl⟩, rfl⟩
  refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
  change cyclicGenerator ^ 1 = cyclicGenerator
  exact pow_one _

/-- The central cyclic factor normally generates the literal normalizer two-core. -/
theorem W_normalClosure :
    normalClosure (W.subgroupOf baseNormalizer : Set baseNormalizer) =
      pCore 2 baseNormalizer := by
  let N := normalClosure (W.subgroupOf baseNormalizer : Set baseNormalizer)
  have hle : N ≤ pCore 2 baseNormalizer := by
    apply normalClosure_le_normal
    intro x hx
    exact (mem_map_iff_mem baseNormalizer.subtype_injective).mp (W_le_A hx)
  let w := CoreGeometry.coreCoordinates (.ofAdd ![1, 2, 0])
  have hw : (w.val : Carrier) = cyclicGenerator.val.val := cyclicGenerator_coordinates.symm
  have hwN : w.val ∈ N := by
    apply subset_normalClosure
    change (w.val : Carrier) ∈ W
    rw [hw]
    exact cyclicGenerator_mem_W
  let e : baseElementary := ⟨e0, subset_closure ⟨0, Fin.le_last 0, rfl⟩⟩
  have he : e ≠ 1 := by
    intro h
    have hh := congrArg (fun x : baseElementary => (x.val : Equiv.Perm (Fin 100)) 1) h
    revert hh
    decide +kernel
  have hwe : CoreGeometry.squareHom w = e := by
    apply Subtype.ext
    rw [CoreGeometry.squareHom_apply, hw]
    exact (congrArg (fun c : core => c.val.val)
      CentralizerRestriction.cyclicGenerator_square).trans commonInvolution_eq_e0
  have hsurj : ∀ x : baseElementary, ∃ q : pCore 2 baseNormalizer,
      q.val ∈ N ∧ CoreGeometry.squareHom q = x := by
    intro x
    by_cases hx : x = 1
    · subst x
      exact ⟨1, N.one_mem, map_one _⟩
    let := elementary_isElementaryAbelian 2
    obtain ⟨α, hα⟩ := ElementaryEightParabolic.automorphism_transitive e x he hx
    obtain ⟨m, hm⟩ : ∃ m : baseNormalizer, baseElementary.normalizerMonoidHom m = α :=
      baseNormalizer_action_surjective α
    refine ⟨MulAut.conjNormal (H := pCore 2 baseNormalizer) m w, ?_, ?_⟩
    · exact (inferInstance : N.Normal).conj_mem w.val hwN m
    · rw [CoreGeometry.squareHom_conjugation, hwe, hm]
      exact hα
  have hEN : ∀ x : baseNormalizer, (x : Carrier) ∈ baseElementary → x ∈ N := by
    intro x hx
    obtain ⟨q, hq, hsq⟩ := hsurj ⟨x.val, hx⟩
    have hpow : q.val ^ 2 = x := by
      apply Subtype.ext
      exact congrArg (fun e : baseElementary => (e : Carrier)) hsq
    rw [← hpow]
    exact N.pow_mem hq 2
  apply le_antisymm hle
  intro a ha
  obtain ⟨q, hq, heq⟩ := hsurj (CoreGeometry.squareHom ⟨a, ha⟩)
  have hker : (⟨a, ha⟩ : pCore 2 baseNormalizer) * q⁻¹ ∈ CoreGeometry.squareHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  rw [CoreGeometry.squareHom_ker] at hker
  have hd : a * q.val⁻¹ ∈ N := hEN _ hker
  simpa only [inv_mul_cancel_right] using N.mul_mem hd hq

/-- The marked involution viewed in the normalizer. -/
@[expose] def j₀Normalizer : baseNormalizer := ⟨j₀, j₀_mem_normalizer⟩

theorem j₀_quotient_order :
    orderOf (QuotientGroup.mk' (pCore 2 baseNormalizer) j₀Normalizer) = 2 := by
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  constructor
  · rw [← map_pow]
    have h : j₀Normalizer ^ 2 = 1 := by
      apply Subtype.ext
      exact j₀_order ▸ pow_orderOf_eq_one j₀
    rw [h, map_one]
  · intro h
    have hm := (QuotientGroup.eq_one_iff _).mp h
    exact j₀_not_mem_A (mem_map_of_mem baseNormalizer.subtype hm)

/-- Every quotient involution is conjugate to the image of the marked pair-kernel involution. -/
theorem quotient_involutions_conjugate_j₀
    (a : baseNormalizer ⧸ pCore 2 baseNormalizer) (ha : orderOf a = 2) :
    ∃ m : baseNormalizer, QuotientGroup.mk' (pCore 2 baseNormalizer) m * a *
      (QuotientGroup.mk' (pCore 2 baseNormalizer) m)⁻¹ =
        QuotientGroup.mk' (pCore 2 baseNormalizer) j₀Normalizer :=
  CoreGeometry.quotient_involutions_conjugate a _ ha j₀_quotient_order

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
