module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases

/-!
# Extracting component actions from full 1.1.5(3)

The universal earlier-result parameter retains all source hypotheses and
all six model/action alternatives. For each nonidentity element of Z,
the hypotheses supplied by 15.4.17 yield a literal automorphism of the
component. Its ambient evaluation proves normalization. The commutator
clause makes the action faithful on each nontrivial ordinary component.

This extraction does not narrow the model alternatives or prove that a
C-component is ordinary. Those are separate source obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(3), printed pp.501–503; proof of 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G]

/-- The actual model action in 1.1.5 normalizes the embedded component. -/
theorem normalizes_of_model_action {H L : Subgroup G} (hLH : L ≤ H) {z : G}
    (h : HasModelAction115 (L.subgroupOf H) z) : z ∈ normalizer (L : Set G) := by
  obtain ⟨α,hα,_⟩ := h
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    let x' : L.subgroupOf H := ⟨⟨x,hLH hx⟩,hx⟩
    change z*x*z⁻¹ ∈ L
    rw [← hα x']
    exact (α x').property
  · intro x hx
    let x' : L.subgroupOf H := ⟨⟨x,hLH hx⟩,hx⟩
    obtain ⟨y,hy⟩ := α.surjective x'
    refine ⟨y,y.property,?_⟩
    change z*(y : G)*z⁻¹ = x
    rw [← hα y,hy]

variable [Finite G]

/-- Apply the full universal earlier result to the hypotheses constructed by
15.4.17. Both normalization and faithfulness follow from its actual action
and commutator clauses. All six model alternatives remain available. -/
theorem component_actions_of_earlier115 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Earlier115Three κ G) {H Z L : Subgroup G}
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (P : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H P M z)
    (hLH : L ≤ H) (hL : IsComponent H (L.subgroupOf H)) :
    Z ≤ normalizer (L : Set G) ∧
      (∀ z ∈ Z, z ≠ 1 → ⁅L,zpowers z⁆ = L) ∧
      Z ⊓ centralizer (L : Set G) = ⊥ ∧
      ∀ z ∈ Z, z ≠ 1 → HasModelAction115 (L.subgroupOf H) z := by
  have hs (z : G) (hz : z ∈ Z) (hne : z ≠ 1) :
      ⁅L,zpowers z⁆ = L ∧ HasModelAction115 (L.subgroupOf H) z := by
    obtain ⟨P,M,h⟩ := hlocal z hz hne
    obtain ⟨hc,_,ha⟩ := earlier hG H P M z h (L.subgroupOf H) hL
    rw [map_subgroupOf_eq_of_le hLH] at hc
    exact ⟨hc.symm,ha⟩
  have hne : L ≠ ⊥ := by
    let : IsQuasisimple (L.subgroupOf H) := hL.2
    let : IsSimpleGroup ((L.subgroupOf H) ⧸ center (L.subgroupOf H)) := IsQuasisimple.simple
    have hn : Nontrivial (L.subgroupOf H) :=
      (QuotientGroup.mk'_surjective (center (L.subgroupOf H))).nontrivial
    intro hh
    exact (nontrivial_iff_ne_bot (L.subgroupOf H)).mp hn (by rw [hh,bot_subgroupOf])
  refine ⟨?_,fun z hz hne => (hs z hz hne).1,
    faithful_of_component_commutators hne (fun z hz hne => (hs z hz hne).1),
    fun z hz hne => (hs z hz hne).2⟩
  intro z hz
  by_cases he : z = 1
  · exact he ▸ (normalizer (L : Set G)).one_mem
  · exact normalizes_of_model_action hLH (hs z hz he).2

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
