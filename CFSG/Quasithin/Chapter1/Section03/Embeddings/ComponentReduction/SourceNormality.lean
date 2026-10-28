module
public import Theory.GroupTheory.GeneralizedFitting.SylowComponentOrbit
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical.SourceAssembly
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound

/-!
# Normality of the detected component orbit

The genuine noncentral structural theorem bounds the component orbit by two.
An actual Sylow-two subgroup meets the nontrivial normalizer coset, so its
conjugate closure is normal in the original overgroup. Together with the
proved supercritical reduction this gives the full normal-or-detected-normal-
orbit alternative. The final conjugate-generation implication consumes
containment of the original complement, whose proof remains separate.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510. The Sylow hypothesis
is explicit, as required by the adequate intrinsic embedding theorem.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.detected_component_orbit_normal
    {p : ℕ} {T X P H L : Subgroup G} (_h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) :
    ((componentOrbit L T).subgroupOf H).Normal := by
  obtain ⟨S, hS⟩ := hT
  let B := L.subgroupOf H
  have hindex : B.Normal ∨ (normalizer (B : Set H)).index = 2 := by
    let := pCore_isNilpotent (p := 2) (G := H)
    apply cComponent_normal_or_index_two_of_quotient hL.mem.2 (pCore 2 H)
    have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
      ⟨quotient_stronglyQuasithin hH.stronglyQuasithin, hH.isKGroup.quotient _⟩
    exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hsq (pCore_quotient_pCore_eq_bot 2) (hL.mem.2.map_quotient _)
  let D := componentOrbit B (S : Subgroup H)
  have hn : D.Normal := componentOrbit_normal_of_normal_or_index_two B S hindex
  have he : D.map H.subtype = componentOrbit L T := by
    rw [map_componentOrbit, map_subgroupOf_eq_of_le hL.mem.1, hS]
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  rw [← he, hd]
  exact hn

theorem LocalInput.normal_or_detected_normal_orbit
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H) :
    (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G,
      ComponentDetection P H L ∧ ((componentOrbit L T).subgroupOf H).Normal := by
  rcases h.normal_or_component_of_fitting_alternative
    (h.quotient_normal_or_fitting_of_source hH.stronglyQuasithin) with hn | ⟨L, hL⟩
  · exact Or.inl hn
  · exact Or.inr ⟨L, hL, h.detected_component_orbit_normal hH hT hL⟩

theorem LocalInput.le_componentOrbit_of_complement_le
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hP : P ≤ componentOrbit L T) :
    X ≤ componentOrbit L T := by
  have hKH : componentOrbit L T ≤ H := (componentOrbit_le_sup L T).trans
    (sup_le hL.mem.1 (le_sup_right.trans h.overgroup))
  exact h.le_of_complement_le hP ((normal_subgroupOf_iff_le_normalizer hKH).mp
    (h.detected_component_orbit_normal hH hT hL))

end CFSG.Quasithin.Chapter1.XiEmbedding
