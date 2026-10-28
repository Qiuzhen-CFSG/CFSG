module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceNormality
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# The detected component orbit is fully moved

The actual SQTK structure gives normality or a normalizer of index two.
The full proved A.3.3(7) dichotomy then makes the detected component orbit
its commutator with the original odd complement. This discharges both
structural premises in the component-containment reduction; containment
of the complement remains the next step.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.detected_component_normal_or_index_two
    {p : ℕ} {T X P H L : Subgroup G} (_h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hL : ComponentDetection P H L) :
    (L.subgroupOf H).Normal ∨ (normalizer (L.subgroupOf H : Set H)).index = 2 := by
  let := pCore_isNilpotent (p := 2) (G := H)
  apply cComponent_normal_or_index_two_of_quotient hL.mem.2 (pCore 2 H)
  have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hH.stronglyQuasithin, hH.isKGroup.quotient _⟩
  exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    hsq (pCore_quotient_pCore_eq_bot 2) (hL.mem.2.map_quotient _)

theorem LocalInput.detected_component_orbit_commutator_source
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) :
    ⁅componentOrbit L T, P⁆ = componentOrbit L T := by
  exact h.detected_component_orbit_commutator
    (fun Y _ _ B D hB => hB.commutator_le_radical_or_eq_iSup_conjugates D) hL
    (h.detected_component_normal_or_index_two hH hL)
    (h.detected_component_orbit_normal hH hT hL)

theorem LocalInput.normal_or_detected_commutator_orbit
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H) :
    (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G,
      ComponentDetection P H L ∧ ((componentOrbit L T).subgroupOf H).Normal ∧
        ⁅componentOrbit L T, P⁆ = componentOrbit L T := by
  rcases h.normal_or_detected_normal_orbit hH hT with hn | ⟨L, hL, hK⟩
  · exact Or.inl hn
  · exact Or.inr ⟨L, hL, hK, h.detected_component_orbit_commutator_source hH hT hL⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
