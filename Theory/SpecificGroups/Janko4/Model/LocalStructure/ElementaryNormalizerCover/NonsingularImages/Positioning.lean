module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Certificate
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Literal Sylow positioning for the nonsingular source images

The full Mathieu centralizer of the Figure 1 pair permutation has order
21504. Its orbit on the eight moved pairs gives order 2688 for the subgroup
preserving the original seed pair. The certified subgroup of order 128
therefore has odd index 21 and is Sylow in this precise quotient container.

An elementary subgroup containing the original 2B seed and the marked pair
permutation has its entire image in the container. Sylow conjugacy lifts
through the surjective quotient of the actual seed centralizer. The lifted
conjugation preserves the seed and pair permutation, puts the whole image
inside the finite certificate, and transports the full ambient centralizer
and normalizer by the same map. No containment of a full ambient Sylow in
the elementary normalizer is assumed.

This supplies the finite domain for the Figure 2 row selection. That selection,
the remaining pure-2A and nonsingular geometry, and the final four-local cover
remain separate obligations. In particular the source positioning premise is
retained explicitly, and no abstract group-family identification replaces it.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Figure 1(b,c)
and Lemma 2.3.1, printed pp.486,492. The original star quotient, seed, native
conjugators and inherited ATLAS coordinate attribution are retained.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Cardinality.QuotientCount.Image ElementaryEightGeometry

open InvolutionCentralizers.Second
open scoped Pointwise

/-- The full centralizer of the literal Figure 1 permutation has order 21504. -/
theorem pairCentralizer_card : Nat.card pairCentralizer = 21504 := by
  let e := starGroupEquivM24
  let q := e pairPermutation
  have hp2 : pairPermutation ^ 2 = 1 := by apply Subtype.ext; decide +kernel
  have hp1 : pairPermutation ≠ 1 := by
    intro he
    have h := congrArg (fun p : StarGroup => p.val 0) he
    change (1 : Fin 24) = 0 at h
    contradiction
  have hq2 : orderOf q = 2 := (e.orderOf_eq _).trans (orderOf_eq_prime hp2 hp1)
  have hqA : IsConj Sporadic.Mathieu.M24InvolutionCentralizers.involution2A q := by
    rcases Sporadic.Mathieu.M24InvolutionCentralizers.involution_classes q hq2 with h | h
    · exact h
    · have he := Sporadic.Mathieu.M24ChapterHStabilizers.class2B_fixed_empty h
      have hf : StarOrderCertificate.relabel 4 ∈
          Sporadic.Mathieu.M24ChapterHStabilizers.fixedPoints q := by
        rw [Sporadic.Mathieu.M24ChapterHStabilizers.mem_fixedPoints]
        change q.val (StarOrderCertificate.relabel 4) = _
        rw [show q.val = MulAut.conj StarOrderCertificate.relabel pairPermutation.val from
          starGroupEquivM24_apply pairPermutation]
        change StarOrderCertificate.relabel (pairPermutation.val
          (StarOrderCertificate.relabel.symm (StarOrderCertificate.relabel 4))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [he] at hf
      exact (Finset.notMem_empty _ hf).elim
  have hmap : pairCentralizer.map e.toMonoidHom = centralizer ({q} : Set Sporadic.Mathieu.M24) := by
    rw [pairCentralizer, map_centralizer_equiv, Set.image_singleton]
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hmap,
    ← card_centralizer_eq_of_isConj _ _ hqA]
  exact Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.centralizer_card

private theorem pair_orbit : MulAction.orbit pairCentralizer starPair = Set.range movingPair := by
  ext A
  constructor
  · rintro ⟨g,rfl⟩
    have hc : g.val.val (pairPermutation.val 0) = pairPermutation.val (g.val.val 0) :=
      congrArg (fun p : StarGroup => p.val 0) (mem_centralizer_singleton_iff.mp g.property)
    have hc' : g.val.val 1 = pairPermutation.val (g.val.val 0) := hc
    have hn : pairPermutation.val (g.val.val 0) ≠ g.val.val 0 := by
      rw [← hc']
      exact g.val.val.injective.ne (by decide)
    obtain ⟨j,hj⟩ := movingPair_exhaustive (g.val.val 0) hn
    refine ⟨j,?_⟩
    change movingPair j = g.val • ({0,1} : Finset (Fin 24))
    rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
    change movingPair j = {g.val.val 0,g.val.val 1}
    rw [hc']
    exact hj.symm
  · rintro ⟨j,rfl⟩
    exact ⟨⟨orbitRep j,orbitRep_mem j⟩,orbitRep_pair j⟩

/-- The eight moved pairs are the exact orbit used in the source stabilizer. -/
theorem container_relIndex : imageContainer.relIndex pairCentralizer = 8 := by
  have hstab : imageContainer.subgroupOf pairCentralizer = MulAction.stabilizer pairCentralizer starPair := by
    ext g
    change (g.val ∈ pairCentralizer ∧ g.val ∈ starPairStabilizer) ↔ _
    exact ⟨And.right,fun h => ⟨g.property,h⟩⟩
  change (imageContainer.subgroupOf pairCentralizer).index = 8
  rw [hstab,MulAction.index_stabilizer,pair_orbit,Set.ncard_range_of_injective movingPair_injective]
  exact Nat.card_fin 8

/-- The marked quotient container has order 2688, with all original maps retained. -/
theorem imageContainer_card : Nat.card imageContainer = 2688 := by
  have h := (imageContainer.subgroupOf pairCentralizer).card_mul_index
  have he : Nat.card (imageContainer.subgroupOf pairCentralizer) = Nat.card imageContainer :=
    Nat.card_congr (subgroupOfEquivOfLe (show imageContainer ≤ pairCentralizer from inf_le_left)).toEquiv
  change Nat.card (imageContainer.subgroupOf pairCentralizer) *
    imageContainer.relIndex pairCentralizer = Nat.card pairCentralizer at h
  rw [he,pairCentralizer_card,container_relIndex] at h
  omega

/-- The certified 128-element subgroup is Sylow in this literal container. -/
def candidateSylow : Sylow 2 imageContainer :=
  (IsPGroup.of_card (p := 2) (n := 7)
    (show Nat.card (candidate.subgroupOf imageContainer) = 128 by
      rw [Nat.card_congr (subgroupOfEquivOfLe candidate_le_container).toEquiv,candidate_card])).toSylow (by
    have hc := (candidate.subgroupOf imageContainer).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe candidate_le_container).toEquiv,
      candidate_card,imageContainer_card] at hc
    have hi : (candidate.subgroupOf imageContainer).index = 21 := by omega
    rw [hi]
    decide)

/-- Every elementary image in the source container is conjugate into the
explicit enumeration; the conjugator still centralizes the marked permutation
and preserves the original seed pair. -/
theorem elementary_container_placement (A : Subgroup StarGroup)
    [IsElementaryAbelian 2 A] (hA : A ≤ imageContainer) :
    ∃ g : imageContainer, A ≤ candidate.map (MulAut.conj (g : StarGroup)).toMonoidHom := by
  let : IsElementaryAbelian 2 (A.subgroupOf imageContainer) := IsElementaryAbelian.subgroupOf hA
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 (A.subgroupOf imageContainer)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq imageContainer candidateSylow S
  refine ⟨g,?_⟩
  intro x hx
  have hs := hS (show (⟨x,hA hx⟩ : imageContainer) ∈ A.subgroupOf imageContainer from hx)
  rw [← hg] at hs
  obtain ⟨y,hy,he⟩ := hs
  refine ⟨y.val,hy,?_⟩
  exact congrArg Subtype.val he

open InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- The original seed and the Figure 1 permutation put the whole elementary
image in the literal source container. No quotient-centralizer table is assumed. -/
theorem source_image_le_container (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom) :
    (X.subgroupOf Local).map starHom ≤ imageContainer := by
  rintro p ⟨x,hx,rfl⟩
  constructor
  · obtain ⟨y,hy,he⟩ := hp
    apply mem_centralizer_singleton_iff.mpr
    rw [← he,← map_mul,← map_mul]
    apply congrArg starHom
    apply Subtype.ext
    exact congrArg (fun x : X => (x : Model)) (mul_comm (⟨x,hx⟩ : X) ⟨y,hy⟩)
  · apply (mem_localCentralizer_iff_star x).mp
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact congrArg (fun x : X => (x : Model)) (mul_comm (⟨x,hx⟩ : X) ⟨seed,hs⟩)

/-- Sylow positioning lifts through the actual seed centralizer. It preserves
the seed and the marked pair permutation, and puts the entire quotient image
in the checked 128-element group. This is the input for the finite Figure 2
row selection, not a completed four-local normalizer cover. -/
theorem source_sylow_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom) :
    ∃ g : localCentralizer,
      starHom g.val ∈ pairCentralizer ∧
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
      pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
      (Y.subgroupOf Local).map starHom ≤ candidate ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom := by
  have hXL : X ≤ Local := X.le_centralizer.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1)
  let A := (X.subgroupOf Local).map starHom
  let : IsElementaryAbelian 2 (X.subgroupOf Local) := IsElementaryAbelian.subgroupOf hXL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map starHom
  obtain ⟨u,hu⟩ := elementary_container_placement A (source_image_le_container X hs hp)
  obtain ⟨g,hg⟩ := toStarPair_surjective (⟨u.val,u.property.2⟩ : starPairStabilizer)
  have hg' : starHom g.val = u.val := congrArg Subtype.val hg
  let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
  have hYL : Y ≤ Local := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      Local.mul_mem (Local.mul_mem (Local.inv_mem g.val.property) (hXL hx)) g.val.property
  have hseed : (MulAut.conj (g.val : Model)⁻¹) seed = (seed : Model) := by
    have hc := congrArg (fun x : Local => (x : Model))
      (mem_centralizer_singleton_iff.mp g.property)
    change (g.val : Model) * (seed : Model) = (seed : Model) * g.val at hc
    change (g.val : Model)⁻¹ * seed * ((g.val : Model)⁻¹)⁻¹ = (seed : Model)
    rw [inv_inv,mul_assoc,← hc,inv_mul_cancel_left]
  have image_forward (x : Local) (hx : (x : Model) ∈ X) :
      starHom (g.val⁻¹ * x * g.val) ∈ (Y.subgroupOf Local).map starHom := by
    apply mem_map_of_mem starHom
    exact mem_map.mpr ⟨x,hx,by simp [mul_assoc]⟩
  refine ⟨g,hg' ▸ u.property.1,hYL,?_,?_,?_,?_,?_⟩
  · rw [← hseed]
    exact mem_map_of_mem (MulAut.conj (g.val : Model)⁻¹).toMonoidHom hs
  · obtain ⟨x,hx,hxp⟩ := hp
    have h := image_forward x hx
    have he : starHom (g.val⁻¹ * x * g.val) = pairPermutation := by
      rw [map_mul,map_mul,map_inv,hg',hxp]
      have hc := mem_centralizer_singleton_iff.mp u.property.1
      rw [mul_assoc,← hc,inv_mul_cancel_left]
    exact he ▸ h
  · rintro p ⟨y,hy,rfl⟩
    obtain ⟨x,hx,he⟩ := hy
    let x0 : Local := ⟨x,hXL hx⟩
    have hye : y = g.val⁻¹ * x0 * g.val := by
      apply Subtype.ext
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, coe_mul, coe_inv, subtype_apply, x0] using he.symm
    obtain ⟨v,hv,hvu⟩ := hu (mem_map_of_mem starHom (show x0 ∈ X.subgroupOf Local from hx))
    rw [hye,map_mul,map_mul,map_inv,hg',← hvu]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, SetLike.mem_coe] using hv

  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g.val : Model)⁻¹)).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g.val : Model)⁻¹)).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
