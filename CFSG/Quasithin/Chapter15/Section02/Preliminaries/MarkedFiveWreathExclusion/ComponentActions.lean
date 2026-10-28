module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveWreathExclusion.ChiefFactors
public import Theory.Representation.BinaryPermutation.FivePairComponents
public import Theory.GroupAction.NormalPChiefSeries.MovedIntersections

/-!
# Both paired chief factors on the actual wreath component

Restrict the original two noncentral chief actions to any C-component K
of H. Each has a natural A₅ moved four-space with kernel O₂(K). The normal
elementary H-span normalizes K, so the moved spaces embed in its literal
intersected sections. Their distinct positions in the original series give
|U_H ∩ K| ≥ 256, hence |O₂(K)| ≥ 256.

The component is the actual subgroup of H, rather than a replacement
abstract A₅ factor. These bounds are applied to the same component selected
by the source reduction, before its W/O₂(W) passage. No survival through
that further quotient is asserted. The mixed-pair exclusion remains with
qt-e-152-small-parabolic.

Source: Aschbacher--Smith 15.1.12 and 15.2.4, printed pp.1090,1105--1107.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- Both original chief intervals retain their kernels and natural moved
four-spaces on the same actual component. -/
theorem ChosenSmallSource.marked_five_wreath_component_chief_actions
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)), ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        ∃ (q : K.subgroupOf H →* alternatingGroup (Fin 5))
          (a : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] Additive (s.Factor k)),
          Function.Surjective q ∧ q.ker = pCore 2 (K.subgroupOf H) ∧
          Function.Injective a ∧
          (∀ g v, a (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (q g) v) =
            s.factorRepresentation k (g : H) (a v)) ∧
          a.range = subspaceCommutator
            ((s.factorRepresentation k).comp (K.subgroupOf H).subtype) ⊤ ⊤ ∧
          Nat.card (subspaceCommutator
            ((s.factorRepresentation k).comp (K.subgroupOf H).subtype) ⊤ ⊤) = 16 := by
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hs⟩ := h.marked_five_wreath_chief_actions hH he l hd s
  refine ⟨i,j,hij,?_⟩
  intro k hk
  obtain ⟨hn,hker,⟨e⟩,_⟩ := hs k hk
  let ρ := s.factorRepresentation k
  let f := e.groupEquiv.toMonoidHom.comp (Representation.BinaryOffender.actionHom ρ)
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp
    ρ.asGroupHom.rangeRestrict_surjective
  have hfk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,hker]
  exact ⟨hn,hker,BinaryPermutation.FivePair.restricted_component_moved
    ρ f hf hfk e.linearEquiv (fun g v => e.intertwines (Representation.BinaryOffender.actionHom ρ g) v)
    (K.subgroupOf H) hK.2⟩

/-- The two moved intervals contribute independently to the original span
intersected with the actual component inside H. -/
theorem ChosenSmallSource.marked_five_wreath_component_span_card
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
      DihedralMarking l 5 2 →
      256 ≤ Nat.card (((conjugateSpan H V).subgroupOf H).subgroupOf (K.subgroupOf H)) := by
  classical
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  let R := K.subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  have hU : U ≤ pCore 2 H := by
    have hc : conjugateSpan H V ≤ H.pCoreIn 2 := by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le (h.prepared.inside_core H hH) (twoCore_normalized H)
    intro x hx
    obtain ⟨y,hy,heq⟩ := hc hx
    exact (Subtype.ext heq : y = x) ▸ hy
  have hN : U ≤ normalizer (R : Set H) := by
    apply hU.trans
    apply le_normalizer_iff_commutator_le_left.mpr
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent (p := 2)
    exact hK.2.commutator_le_of_solvable _ (by rw [normalizer_eq_top]; exact le_top)
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.marked_five_wreath_component_chief_actions hH he hK l hd s
  obtain ⟨_,_,q₀,a₀,_,_,_,_,_,hi⟩ := hs i (by simp)
  obtain ⟨_,_,q₁,a₁,_,_,_,_,_,hj⟩ := hs j (by simp)
  have hb := s.two_moved_cards_le_intersection R hN i j hij
  rw [hi,hj] at hb
  exact hb

/-- Transport the intersection bound to the ambient subgroup and its
intrinsic two-core, retaining the original component embedding. -/
theorem ChosenSmallSource.marked_five_wreath_component_bounds
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
      DihedralMarking l 5 2 →
      256 ≤ Nat.card (conjugateSpan H V ⊓ K : Subgroup G) ∧
      256 ≤ Nat.card (pCore 2 K) := by
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  let R := K.subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hb := h.marked_five_wreath_component_span_card hH he hK l hd
  have hm : ((U.subgroupOf R).map R.subtype).map H.subtype = conjugateSpan H V ⊓ K := by
    rw [subgroupOf_map_subtype,map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hK.1]
  have hc := card_map_of_injective (K := U.subgroupOf R)
    (f := H.subtype.comp R.subtype) (H.subtype_injective.comp R.subtype_injective)
  change Nat.card ((U.subgroupOf R).map (H.subtype.comp R.subtype)) = _ at hc
  rw [←map_map,hm] at hc
  refine ⟨hc.symm ▸ hb,?_⟩
  have hU : U ≤ pCore 2 H := by
    have hcore : conjugateSpan H V ≤ H.pCoreIn 2 := by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le (h.prepared.inside_core H hH) (twoCore_normalized H)
    intro x hx
    obtain ⟨y,hy,heq⟩ := hcore hx
    exact (Subtype.ext heq : y = x) ▸ hy
  have hRK : U.subgroupOf R ≤ pCore 2 R := by
    rw [pCore_subnormal_eq_comap 2 hK.2.subnormal]
    exact subgroupOf_mono R hU
  have hbound := hb.trans (card_le_of_le hRK)
  let e := subgroupOfEquivOfLe hK.1
  have hcard : Nat.card (pCore 2 R) = Nat.card (pCore 2 K) := by
    rw [←pCore_map_iso 2 e,card_map_of_injective e.injective]
  rwa [hcard] at hbound

end CFSG.Quasithin.Chapter15.Section02
