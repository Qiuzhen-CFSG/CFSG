module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainedBlockModule
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import Theory.GroupTheory.CComponent.ContainedGeneralizedFitting
/-!
# The genuine index-two branch for the normalized A₅ C28 source

When the generalized Fitting preimage of H is contained in M, the unchanged
A₅ module is forced into O₂(H). The corresponding quotient image of L is a
perfect central cover of A₅ and hence an ordinary component of H. The
original normalizer equality and the orbit bound then force M to have index
2. This is the source case (10) reduction, with all quotient maps literal.

Source: Aschbacher–Smith C.2.13 and C.4.8(10), printed pp.148,153.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}
/-- The source L is an actual ambient C-component in the contained branch. -/
theorem original_component_of_fitting_contained
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hnorm : M ≤ normalizer (L : Set G))
    (hU : (blockU L).map L.subtype = V)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    (L.subgroupOf H).IsCComponent := by
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hLH : L ≤ H := h.component_le.trans h.local_le
  let A := L.subgroupOf H
  let N := M.subgroupOf H
  let e : A ≃* L := subgroupOfEquivOfLe hLH
  let : Group.IsPerfect L := hs ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hAN : A ≤ N := comap_mono h.component_le
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hLH]
    exact comap_mono hnorm
  have hQN : pCore 2 H ≤ N := by
    intro x hx
    exact h.radical_le (h.ambient_core_le_radical (mem_map_of_mem H.subtype hx))
  have hu := h.block_module_le_ambient_core_of_fitting_contained hnorm hU hf
  have hU' : (⁅pCore 2 A,(⊤ : Subgroup A)⁆).map A.subtype ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    have hmap : (⁅pCore 2 A,(⊤ : Subgroup A)⁆).map (H.subtype.comp A.subtype) = V := by
      have he : H.subtype.comp A.subtype = L.subtype.comp e.toMonoidHom := by ext x; rfl
      rw [he,←map_map,map_commutator,pCore_map_iso,
        map_top_of_surjective _ e.surjective]
      exact hU
    rw [map_map,hmap]
    exact hu
  exact isCComponent_of_contained_generalizedFitting A N hAN hNA hQN hU' hf

/-- Strict local containment forces the original index-two alternative. -/
theorem index_two_of_fitting_contained
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hnorm : M ≤ normalizer (L : Set G)) (hstrict : M < H)
    (hU : (blockU L).map L.subtype = V)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    (L.subgroupOf H).IsCComponent ∧ (M.subgroupOf H).index = 2 := by
  have hc := h.original_component_of_fitting_contained hnorm hU hf
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hn : normalizer (L.subgroupOf H : Set H) = M.subgroupOf H := by
    have he := h.normalizer_span_eq
    rw [hs] at he
    rw [←subgroupOf_normalizer_eq (h.component_le.trans h.local_le)]
    ext x
    exact ⟨fun hx => (he ▸ (show (x : G) ∈ H ⊓ normalizer (L : Set G) from ⟨x.property,hx⟩)),
      fun hx => (show (x : G) ∈ H ⊓ normalizer (L : Set G) from he.symm ▸ hx).2⟩
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hc with hN | hi
  · let := hN
    have ht : M.subgroupOf H = ⊤ := hn.symm.trans (normalizer_eq_top (L.subgroupOf H))
    exact (not_le_of_gt hstrict (subgroupOf_eq_top.mp ht)).elim
  · exact ⟨hc,hn ▸ hi⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
