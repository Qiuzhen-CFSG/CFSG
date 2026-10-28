module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.ExactSource
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondCharacter

/-!
# Marking an outer involution in the original seed centralizer

A fixed-point involution of the Mathieu quotient is in class 2A. Correcting
its conjugator by a moved-pair orbit representative keeps the original seed
pair fixed. The literal seed-centralizer lift then positions the entire
ambient elementary group. Exact-row refinement is applied with the composed
ambient conjugator and the same full centralizer and normalizer maps.

The alternative fixed-point-free quotient involution is retained explicitly;
its ABB(3) enlargement remains a source obligation.
Source: Kleidman--Wilson (1988), Section 2.3 and Lemma 2.3.1, printed p.492.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Subgroup Theory.GroupTheory Cardinality.QuotientCount.Image ElementaryEightGeometry
open InvolutionCentralizers.Second
open scoped Pointwise

private theorem class_twoA_of_fixed (q : StarGroup) (hq : orderOf q = 2)
    (hfix : ∃ x : Fin 24, q.val x = x) :
    IsConj Sporadic.Mathieu.M24InvolutionCentralizers.involution2A (starGroupEquivM24 q) := by
  rcases Sporadic.Mathieu.M24InvolutionCentralizers.involution_classes (starGroupEquivM24 q)
      ((starGroupEquivM24.orderOf_eq _).trans hq) with h | h
  · exact h
  · obtain ⟨x,hx⟩ := hfix
    have he := Sporadic.Mathieu.M24ChapterHStabilizers.class2B_fixed_empty h
    have hf : StarOrderCertificate.relabel x ∈
        Sporadic.Mathieu.M24ChapterHStabilizers.fixedPoints (starGroupEquivM24 q) := by
      rw [Sporadic.Mathieu.M24ChapterHStabilizers.mem_fixedPoints]
      change (starGroupEquivM24 q).val (StarOrderCertificate.relabel x) = _
      rw [starGroupEquivM24_apply]
      change StarOrderCertificate.relabel (q.val
        (StarOrderCertificate.relabel.symm (StarOrderCertificate.relabel x))) = _
      rw [Equiv.symm_apply_apply,hx]
    rw [he] at hf
    exact (Finset.notMem_empty _ hf).elim

private theorem pair_order : orderOf pairPermutation = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext; decide +kernel
  · intro h
    have he := congrArg (fun q : StarGroup => q.val 0) h
    change (1 : Fin 24) = 0 at he
    contradiction

/-- Every fixed-point involution swapping the original seed pair is conjugate
to the marked Figure 1 permutation by a conjugator preserving that same pair. -/
theorem fixed_involution_pair_positioning (q : StarGroup) (hq : orderOf q = 2)
    (h0 : q.val 0 = 1) (hfix : ∃ x : Fin 24, q.val x = x) :
    ∃ g : starPairStabilizer, MulAut.conj (g : StarGroup) pairPermutation = q := by
  have hpA := class_twoA_of_fixed pairPermutation pair_order ⟨4,rfl⟩
  have hqA := class_twoA_of_fixed q hq hfix
  have hc : IsConj pairPermutation q := by
    have h := starGroupEquivM24.symm.toMonoidHom.map_isConj (hpA.symm.trans hqA)
    simpa using h
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hpair : pairPermutation.val (g.val.symm 0) = g.val.symm 1 := by
    have h := congrArg g.val.symm h0
    rw [← hg] at h
    simpa only [coe_mul,coe_inv,Equiv.Perm.coe_mul,Function.comp_apply,
      Equiv.Perm.coe_inv,Equiv.symm_apply_apply] using h
  have hm : pairPermutation.val (g.val.symm 0) ≠ g.val.symm 0 := by
    rw [hpair]
    exact g.val.symm.injective.ne (by decide)
  obtain ⟨j,hj⟩ := movingPair_exhaustive (g.val.symm 0) hm
  have hr : orbitRep j • starPair = g⁻¹ • starPair := by
    rw [orbitRep_pair,← hj,hpair]
    change {g.val.symm 0,g.val.symm 1} = g⁻¹ • ({0,1} : Finset (Fin 24))
    rw [Finset.smul_finset_insert,Finset.smul_finset_singleton]
    rfl
  have hu : g * orbitRep j ∈ starPairStabilizer := by
    change (g * orbitRep j) • starPair = starPair
    rw [mul_smul,hr,smul_inv_smul]
  refine ⟨⟨g * orbitRep j,hu⟩,?_⟩
  have hrep := mem_centralizer_singleton_iff.mp (orbitRep_mem j)
  change (g * orbitRep j) * pairPermutation * (g * orbitRep j)⁻¹ = q
  rw [mul_inv_rev,mul_assoc,mul_assoc,← mul_assoc (orbitRep j) pairPermutation,hrep]
  simpa [mul_assoc] using hg

open LargeCenterRadicals.OuterHalf
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- An outer involution in the original seed centralizer either has a
fixed-point-free Mathieu image, or yields the exact marked Figure 1 image
by a literal seed-centralizer conjugation of the entire elementary group. -/
theorem source_outer_pair_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (y : Model) (hy : y ∈ X)
    (houter : ¬ InnerRelated (seed : Model) y) :
    (∃ z : Local, (z : Model) ∈ X ∧ orderOf (starHom z) = 2 ∧
      ∀ x : Fin 24, (starHom z).val x ≠ x) ∨
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
      pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom) := by
  have hXL : X ≤ Local := X.le_centralizer.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1)
  let z : Local := ⟨y,hXL hy⟩
  have hz : z ∈ localCentralizer := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact congrArg (fun a : X => (a : Model)) (mul_comm (⟨y,hy⟩ : X) ⟨seed,hs⟩)
  have hpair : starHom z ∈ starPairStabilizer := (mem_localCentralizer_iff_star z).mp hz
  have h0 : (starHom z).val 0 = 1 := by
    have hmem (i : Fin 24) (hi : i ∈ starPair) : (starHom z).val i ∈ starPair :=
      MulAction.mem_stabilizer_finset'.mp hpair hi
    have hzero := hmem 0 (by simp [starPair])
    have hone := hmem 1 (by simp [starPair])
    simp only [starPair,Finset.mem_insert,Finset.mem_singleton] at hzero hone
    rcases hzero with h0 | h0
    · exfalso
      have h1 : (starHom z).val 1 = 1 := hone.resolve_left (fun h =>
        (by decide : (1 : Fin 24) ≠ 0) ((starHom z).val.injective (h.trans h0.symm)))
      exact houter ((innerRelated_second_iff_star ⟨z,hz⟩).mpr ⟨h0,h1⟩)
    · exact h0
  have hq : orderOf (starHom z) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hz2 : z ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy)
      rw [hz2,map_one]
    · intro he
      have ht := congrArg (fun p : StarGroup => p.val 0) he
      rw [h0] at ht
      contradiction
  by_cases hf : ∃ x : Fin 24, (starHom z).val x = x
  · obtain ⟨u,hu⟩ := fixed_involution_pair_positioning (starHom z) hq h0 hf
    obtain ⟨g,hg⟩ := toStarPair_surjective u
    have hg' : starHom g.val = u.val := congrArg Subtype.val hg
    let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
    right
    refine ⟨g,?_,?_,?_,?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
        Local.mul_mem (Local.mul_mem (Local.inv_mem g.val.property) (hXL hx)) g.val.property
    · have hc := congrArg (fun a : Local => (a : Model))
        (mem_centralizer_singleton_iff.mp g.property)
      have he : MulAut.conj (g.val : Model)⁻¹ (seed : Model) = seed := by
        change (g.val : Model) * (seed : Model) = (seed : Model) * g.val at hc
        change (g.val : Model)⁻¹ * seed * ((g.val : Model)⁻¹)⁻¹ = _
        rw [inv_inv,mul_assoc,← hc,inv_mul_cancel_left]
      exact he ▸ mem_map_of_mem (MulAut.conj (g.val : Model)⁻¹).toMonoidHom hs
    · let z' : Local := g.val⁻¹ * z * g.val
      have hz' : (z' : Model) ∈ Y := mem_map.mpr ⟨y,hy,by simp [z',z,mul_assoc]⟩
      have he : starHom z' = pairPermutation := by
        dsimp only [z']
        rw [map_mul,map_mul,map_inv,hg',← hu]
        simp [mul_assoc]
      exact he ▸ mem_map_of_mem starHom (show z' ∈ Y.subgroupOf Local from hz')
    · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g.val : Model)⁻¹)).symm
    · exact (map_equiv_normalizer_eq X (MulAut.conj (g.val : Model)⁻¹)).symm
  · exact Or.inl ⟨z,hy,hq,by simpa only [not_exists] using hf⟩

/-- Exact source rows after positioning an arbitrary outer pair with a
fixed-point quotient image. The unresolved fixed-point-free case is explicit. -/
theorem source_outer_exact_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (y : Model) (hy : y ∈ X)
    (houter : ¬ InnerRelated (seed : Model) y) :
    (∃ z : Local, (z : Model) ∈ X ∧ orderOf (starHom z) = 2 ∧
      ∀ x : Fin 24, (starHom z).val x ≠ x) ∨
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
      pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
      ((Y.subgroupOf Local).map starHom ≤ boxImage ∨
        ∃ k : Fin 5, (Y.subgroupOf Local).map starHom = Refinement.exactRow k) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom) := by
  rcases source_outer_pair_positioning X hs y hy houter with h | ⟨u,huL,hus,hup,_,_⟩
  · exact Or.inl h
  let Z := X.map (MulAut.conj (u.val : Model)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  obtain ⟨v,_,hvL,hvs,hvp,hrow,_,_⟩ := source_exact_row_positioning Z hus hup
  let g : localCentralizer := u * v
  have he : Z.map (MulAut.conj (v.val : Model)⁻¹).toMonoidHom =
      X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [g,mul_assoc]
  right
  refine ⟨g,he ▸ hvL,he ▸ hvs,he ▸ hvp,he ▸ hrow,?_,?_⟩
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g.val : Model)⁻¹)).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g.val : Model)⁻¹)).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
