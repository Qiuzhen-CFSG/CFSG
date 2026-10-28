module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.NormalizedRestriction
/-!
# The literal component-orbit reduction in normalized C.2.8

Choose a Sylow subgroup of the original M containing R. The subgroup generated
by that Sylow, the unchanged L, and the actual Sylow orbit of an escaping K
inherits C.2.8 and remains strictly larger than its intersection with M.
No Sylow subgroup of H and no normalization of K by R are assumed.

Source: Aschbacher–Smith C.2.9(3), C.3.1 and C.4.2, pp.147,149,152.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}
/-- The original escaping component supplies the actual reduced source configuration. -/
theorem normalized_orbit_reduction (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G)) (K : Subgroup H)
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ T : Sylow 2 M, R ≤ (T : Subgroup M).map M.subtype ∧
      let N := conjugateSpanBy (K.map H.subtype) ((T : Subgroup M).map M.subtype) ⊔
        L ⊔ (T : Subgroup M).map M.subtype
      N ≤ H ∧ K.map H.subtype ≤ N ∧ M ⊓ N < N ∧
        HypothesisC28 κ N (M ⊓ N) L R V := by
  obtain ⟨T,hRT⟩ := (h.radical_isTwoGroup.comap_subtype (K := M)).exists_le_sylow
  have hRT' : R ≤ (T : Subgroup M).map M.subtype := by
    intro r hr
    exact ⟨⟨r,h.radical_le hr⟩,hRT hr,rfl⟩
  refine ⟨T,hRT',?_⟩
  let P := (T : Subgroup M).map M.subtype
  let A := conjugateSpanBy (K.map H.subtype) P
  let N := A ⊔ L ⊔ P
  have hPH : P ≤ H := (map_subtype_le _).trans h.local_le
  have hAH : A ≤ H := conjugateSpanBy_le (map_subtype_le _) (hPH.trans H.le_normalizer)
  have hLH : L ≤ H := h.component_le.trans h.local_le
  have hNH : N ≤ H := sup_le (sup_le hAH hLH) hPH
  have hKN : K.map H.subtype ≤ N := (le_conjugateSpanBy _ _).trans (le_sup_left.trans le_sup_left)
  have hLN : L ≤ N := le_sup_right.trans le_sup_left
  have hlt : M ⊓ N < N := lt_of_le_of_ne inf_le_right (by
    intro he
    apply hout
    intro k hk
    have hn := hKN (mem_map_of_mem H.subtype hk)
    rw [←he] at hn
    exact hn.1)
  exact ⟨hNH,hKN,hlt,h.restrict_normalized_over_sylow hnorm T hRT' le_sup_right hLN hNH⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
