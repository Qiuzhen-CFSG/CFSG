module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.PairOrder
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.SourceLifts

/-!
# Assembly of elementary max2 quotient incidence

The source elementary pair injects into the certified matrix quotient, and
its Sylow witness and setwise permutability descend. Finite incidence chooses
one of two concrete candidates and a quotient conjugator. Surjectivity lifts
the conjugator to H, and a fixed inverse-image placement then gives an actual
ambient max4 conjugate. The entire two-core is retained because it lies in S.

The finite incidence and both inverse-image placements remain explicit
premises. This module does not yet prove the unconditional source contract.
Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), and its reference [Asc86b].
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup max4Subgroup

private theorem le_conjugate_of_image_le {G A : Type*} [Group G] [Group A]
    (f : G →* A) (B : Subgroup A) (M K : Subgroup G) (a : G)
    (hpre : B.comap f ≤ M)
    (himage : K.map f ≤ B.map (MulAut.conj (f a)).toMonoidHom) :
    K ≤ M.map (MulAut.conj a).toMonoidHom := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := himage (mem_map_of_mem f hx)
  refine ⟨a⁻¹ * x * a, hpre ?_, ?_⟩
  · change f (a⁻¹ * x * a) ∈ B
    rw [map_mul, map_mul, map_inv, ← hbx]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one, SetLike.mem_coe] using hb
  · change a * (a⁻¹ * x * a) * a⁻¹ = x
    simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]

private theorem source_conjugate_overlap_le (a : sourceSubgroup) (g : Janko4.Model) :
    (involutionSourceMax4Overlap g).map (MulAut.conj a).toMonoidHom ≤
      involutionSourceMax4Overlap ((a : Janko4.Model) * g) := by
  rintro x ⟨y, hy, hxy⟩
  change (y : Janko4.Model) ∈ max4Subgroup.map (MulAut.conj g).toMonoidHom at hy
  obtain ⟨z, hz, hzy⟩ := hy
  change (x : Janko4.Model) ∈ max4Subgroup.map
    (MulAut.conj ((a : Janko4.Model) * g)).toMonoidHom
  refine ⟨z, hz, ?_⟩
  have h := congrArg (fun t : sourceSubgroup => (t : Janko4.Model)) hxy
  change (a : Janko4.Model) * (y : Janko4.Model) * (a : Janko4.Model)⁻¹ = x at h
  rw [← h, ← hzy]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, mul_assoc]

/-- Assembly from finite quotient incidence and the two concrete inverse-image
placements. Both inputs remain genuine, independent proof obligations. -/
theorem elementaryInvolutionQuotientIncidence_of_matrix_incidence
    (hinc : ElementaryMatrixIncidence) (hlift : InvolutionMatrixOverlapLift) :
    ElementaryInvolutionQuotientIncidence := by
  intro _ _ _ S R h hE hcard hS hR
  let e := involutionSourceMatrixQuotientEquiv
  let S' := (involutionSourceQuotientSylow S hS).mapSurjective
    (f := e.toMonoidHom) e.surjective
  let R' := (involutionSourceQuotientImage R).map e.toMonoidHom
  have hS' : (S' : Subgroup LowerBound.quotientSubgroup) =
      (involutionSourceQuotientImage (S : Subgroup Janko4.Model)).map e.toMonoidHom := rfl
  have hE' : IsElementaryAbelian 3 R' := by
    let _ := involutionSource_quotient_elementary hR hE
    exact IsElementaryAbelian.map e.toMonoidHom
  have hc' : Nat.card R' = 3 ^ 2 :=
    (Nat.card_congr (e.subgroupMap (involutionSourceQuotientImage R)).toEquiv).symm.trans
      (involutionSource_quotient_card hR hE hcard)
  have hp' : (R' : Set LowerBound.quotientSubgroup) * (S' : Set LowerBound.quotientSubgroup) =
      (S' : Set LowerBound.quotientSubgroup) * (R' : Set LowerBound.quotientSubgroup) := by
    change (R' : Set LowerBound.quotientSubgroup) *
        ((S' : Subgroup LowerBound.quotientSubgroup) : Set LowerBound.quotientSubgroup) =
      ((S' : Subgroup LowerBound.quotientSubgroup) : Set LowerBound.quotientSubgroup) *
        (R' : Set LowerBound.quotientSubgroup)
    rw [hS']
    have hp := congrArg (Set.image e)
      (involutionSource_quotient_permutes S R h hS hR)
    simpa only [R', S', Sylow.coe_mapSurjective, Sylow.coe_coe,
      involutionSourceQuotientSylow_coe, coe_map, Set.image_mul,
      MulEquiv.coe_toMonoidHom] using hp
  obtain ⟨i, u, hu⟩ := hinc S' R' hE' hc' hp'
  rw [hS'] at hu
  obtain ⟨a, ha⟩ := involutionSourceMatrixMap_surjective u
  obtain ⟨g, hg⟩ := hlift i
  have himage : ((R ⊔ (S : Subgroup Janko4.Model)).subgroupOf sourceSubgroup).map
      involutionSourceMatrixMap ≤ (involutionMatrixCandidate i).map
        (MulAut.conj (involutionSourceMatrixMap a)).toMonoidHom := by
    rw [ha, subgroupOf_sup hR hS, Subgroup.map_sup]
    simpa only [R', S', Sylow.coe_mapSurjective, involutionSourceQuotientSylow_coe,
      involutionSourceQuotientImage, map_map, e, involutionSourceMatrixMap] using hu
  have hle := (le_conjugate_of_image_le involutionSourceMatrixMap
    (involutionMatrixCandidate i) (involutionSourceMax4Overlap g)
    ((R ⊔ (S : Subgroup Janko4.Model)).subgroupOf sourceSubgroup) a hg himage).trans
      (source_conjugate_overlap_le a g)
  refine ⟨(a : Janko4.Model) * g, ?_, map_mono hle⟩
  exact (involutionSource_twoCore_le_sylow S hS).trans
    ((comap_mono le_sup_right).trans hle)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
