module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionDisjoint
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionCubic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionIsotypic
/-!
# Full isotypic summands for the literal chosen seed

The two marked unchanged-L types give complementary full isotypic components
inside U = componentOrbit V (normalizer L). The action is the original
conjugation action. Every element of its faithful image permutes the two
subspaces. A moving element of the original Sylow T interchanges them, and
strict enlargement of U over componentOrbit V T makes the seed strictly
smaller than its full isotypic component.

The final application supplies this decomposition, its dimension greater
than two, and the minimal cubic actor in the original Sylow image with
trivial two-core. These are the inputs to D.2.9(6) at D.3.12. Cubic
stabilization, the later centralizer exclusions and the final Source325
assembly remain with qt-baumann-fsu; no multiplicity bound is inferred here.
Source: Aschbacher--Smith D.3.10--12, printed pp.201--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Two full, complementary type components in the original normalizer orbit.
A strict enlargement forces an actual strict inclusion in the first component. -/
theorem normalizer_isotypic_pair_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    letI : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
    let c := normalTypeAction (internalAction hn) (L.subgroupOf M)
    let S := internalSubrepresentation hn D.normalizes
    IsIrreducible S.toRepresentation ∧
    ∃ t : M, t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
      IsCompl (typePart S) (c.conjugate t (typePart S)) ∧
      (∀ g : M, c.conjugate g (typePart S) = typePart S ∨
        c.conjugate g (typePart S) = c.conjugate t (typePart S)) ∧
      (U ≠ componentOrbit V (T : Subgroup G) → S < typePart S) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let c := normalTypeAction (internalAction hn) (L.subgroupOf M)
  let S := internalSubrepresentation hn D.normalizes
  let := D.elementary
  have hVU : V ≤ U := le_componentOrbit V M
  have hconj (g : M) : c.conjugate g S =
      internalSubrepresentation hn (normalizes_conjugate D.normalizes g) :=
    internal_conjugate_subrepresentation hn le_rfl hVU D.normalizes g
  have hle (g : M) : V.map (MulAut.conj g.val).toMonoidHom ≤ U := by
    change V.map (MulAut.conj g.val).toMonoidHom ≤
      ⨆ z : M, V.map (MulAut.conj z.val).toMonoidHom
    exact le_iSup (fun z : M => V.map (MulAut.conj z.val).toMonoidHom) g
  have hsame (g : M) : SameModule S (c.conjugate g S) ↔
      SameConjugationModule L V (V.map (MulAut.conj g.val).toMonoidHom) := by
    let : IsElementaryAbelian 2 (V.map (MulAut.conj g.val).toMonoidHom) :=
      IsElementaryAbelian.of_le (hle g)
    rw [hconj]
    exact ⟨sameConjugationModule_of_internal hn L.le_normalizer hVU (hle g) D.normalizes
      (normalizes_conjugate D.normalizes g), same_internalSubrepresentation hn hVU (hle g)
        D.normalizes (normalizes_conjugate D.normalizes g)⟩
  have hi : IsIrreducible S.toRepresentation :=
    internalSubrepresentation_irreducible hn L.le_normalizer hVU D.normalizes D.ne_bot
      (D.seed_invariant_subgroup_eq hc)
  obtain ⟨t,ht,hnt,_,_,hntype,htypes⟩ := D.normalizer_type_pair_of_moved_of_many h hmany hc hm
  let t' : M := ⟨t,D.sylow_normalizes_component ht⟩
  have ht' : ¬ SameModule S (c.conjugate t' S) := fun he => hntype ((hsame t').mp he)
  have htypes' (g : M) : SameModule S (c.conjugate g S) ∨
      SameModule (c.conjugate t' S) (c.conjugate g S) := by
    rcases htypes g.val g.property with he | he
    · exact Or.inl ((hsame g).mpr he)
    · right
      let : IsElementaryAbelian 2 (V.map (MulAut.conj g.val).toMonoidHom) :=
        IsElementaryAbelian.of_le (hle g)
      let : IsElementaryAbelian 2 (V.map (MulAut.conj t'.val).toMonoidHom) :=
        IsElementaryAbelian.of_le (hle t')
      rw [hconj,hconj]
      exact same_internalSubrepresentation hn (hle t') (hle g)
        (normalizes_conjugate D.normalizes t') (normalizes_conjugate D.normalizes g) he
  have hspan : c.span S = ⊤ :=
    internal_typeAction_span_eq_top hn le_rfl hVU D.normalizes rfl
  refine ⟨hi,t',ht,hnt,?_,?_,?_⟩
  · rw [conjugate_typePart]
    exact two_typeParts_complement c S hi t' ht' htypes' hspan
  · intro g
    rw [conjugate_typePart c S t']
    exact two_typeParts_permuted c S t' htypes' g
  · intro hne
    obtain ⟨g,hg,he,_,hout⟩ := D.exists_repeated_disjoint_conjugate_of_normalizerOrbit_ne
      h hmany hc hm hne
    let g' : M := ⟨g,hg⟩
    have hgs : c.conjugate g' S ≤ typePart S := by
      rw [typePart_eq_of_same ((hsame g').mpr he)]
      exact le_typePart _
    apply lt_of_le_of_ne (le_typePart S)
    intro heq
    rw [←heq,hconj] at hgs
    have hv : V.map (MulAut.conj g).toMonoidHom ≤ V := by
      intro v hv
      exact hgs (show Additive.ofMul (⟨v,hle g' hv⟩ : U) ∈
        internalSubrepresentation hn (normalizes_conjugate D.normalizes g') from hv)
    exact hout (hv.trans (le_componentOrbit V T))

/-- The literal faithful-image input to D.2.9(6): a permuted complementary
pair of dimension greater than two and a minimal cubic actor in the original
Sylow image, with no two-core. This does not yet assert actor stabilization. -/
theorem normalizer_starred_isotypic_pair_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    ∃ t : M, t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
      IsCompl I (I.map (ρ (internalHom M U hn t))) ∧
      internalSection U V < I ∧
      2 < Module.finrank (ZMod 2) I ∧
      (∀ a : internalActionImage M U hn, I.map (ρ a) = I ∨
        I.map (ρ a) = I.map (ρ (internalHom M U hn t))) ∧
      ∃ A : Subgroup (internalActionImage M U hn),
        A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧
        A ∈ QhatStar ρ ∧ pCore 2 (internalActionImage M U hn) = ⊥ := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let c := normalTypeAction (internalAction hn) (L.subgroupOf M)
  let S := internalSubrepresentation hn D.normalizes
  let I := (typePart S).toSubmodule
  obtain ⟨_,t,ht,hnt,hcomp,hperm,hstrict⟩ :=
    D.normalizer_isotypic_pair_of_moved_of_many h hmany hc hm
  have hmap (g : M) : (c.conjugate g (typePart S)).toSubmodule =
      I.map (ρ (internalHom M U hn g)) :=
    conjugateSubrepresentationOrderIso_toSubmodule (internalAction hn) (L.subgroupOf M) g _
  have hstrict' : internalSection U V < I := by
    have hs := hstrict hne
    exact lt_of_le_of_ne hs.le (fun he => hs.ne (Subrepresentation.toSubmodule_injective he))
  refine ⟨t,ht,hnt,?_,hstrict',?_,?_,?_⟩
  · constructor
    · apply disjoint_iff.mpr
      have he := congrArg Subrepresentation.toSubmodule hcomp.disjoint.eq_bot
      change I ⊓ (c.conjugate t (typePart S)).toSubmodule = ⊥ at he
      rwa [hmap] at he
    · apply codisjoint_iff.mpr
      have he := congrArg Subrepresentation.toSubmodule hcomp.sup_eq_top
      change I ⊔ (c.conjugate t (typePart S)).toSubmodule = ⊤ at he
      rwa [hmap] at he
  · let := D.elementary
    let a : D.space ≃+ Additive V := D.spaceEquiv.toAdditive
    let e : D.space ≃ₗ[ZMod 2] Additive V :=
      { a with map_smul' := ZMod.map_smul a }
    have hd : 2 < Module.finrank (ZMod 2) (internalSection U V) := by
      rw [(internalSectionEquiv (le_componentOrbit V M)).finrank_eq,←e.finrank_eq,
        ←D.orbitSeedActionEquiv.linearEquiv.finrank_eq]
      exact D.orbitSeed_finrank_gt_two h.toHypothesis1221
    exact hd.trans_le (Submodule.finrank_mono hstrict'.le)
  · intro a
    obtain ⟨g,rfl⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective a
    rcases hperm g with he | he
    · exact Or.inl ((hmap g).symm.trans (congrArg Subrepresentation.toSubmodule he))
    · exact Or.inr ((hmap g).symm.trans
        ((congrArg Subrepresentation.toSubmodule he).trans (hmap t)))
  · obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
    exact ⟨A,hAS,hA,D.normalizerActor_twoCore_eq_bot h.toHypothesis1221⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
