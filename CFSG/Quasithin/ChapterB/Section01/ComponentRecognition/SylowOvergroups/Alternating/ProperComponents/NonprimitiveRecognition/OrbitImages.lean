module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.SmallDegrees
public import Theory.GroupTheory.GeneralizedFitting.ComponentFaithfulImages

/-!
# Faithful orbit images and actual component isomorphisms

The projection is the range restriction of the natural action on each
orbit. These literal maps jointly separate elements, so centerlessness
of all component images eliminates every central kernel simultaneously.
A nontrivial orbit image is therefore isomorphic to the original component.
No Sylow property of these images, or parity condition, is assumed proved.

Source: the orbit reduction in the alternating-overgroup argument of
Aschbacher–Smith B.1.13, printed p.74 (PDF p.85).
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
open Theory.GroupTheory MulAction

abbrev alternatingOrbitImage {m : ℕ} (X : Subgroup (alternatingGroup (Fin m)))
    (a : Fin m) := (MulAction.toPermHom X (orbit X a)).range

@[expose] def alternatingOrbitProjection {m : ℕ} (X : Subgroup (alternatingGroup (Fin m)))
    (a : Fin m) : X →* alternatingOrbitImage X a :=
  (MulAction.toPermHom X (orbit X a)).rangeRestrict

theorem alternatingOrbitProjection_separates {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m))) (g : X)
    (hg : ∀ a, alternatingOrbitProjection X a g = 1) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact congrArg (fun p : alternatingOrbitImage X a =>
    (p.val ⟨a, mem_orbit_self a⟩).val) (hg a)

theorem alternating_component_equiv_orbit_image {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m)))
    (D : Subgroup X) (hD : IsComponent X D)
    (hcenter : ∀ a, center (D.map (alternatingOrbitProjection X a)) = ⊥) :
    ∃ a, IsComponent (alternatingOrbitImage X a)
      (D.map (alternatingOrbitProjection X a)) ∧
      Nonempty (D ≃* D.map (alternatingOrbitProjection X a)) :=
  hD.exists_equiv_image_of_separating_homs (alternatingOrbitProjection X)
    (fun a => (MulAction.toPermHom X (orbit X a)).rangeRestrict_surjective)
    (alternatingOrbitProjection_separates X) hcenter

/-- Classification in the actual orbit-action images gives the full source
model for a component, including an isomorphism rather than a central quotient.
The image models retain the original ambient bound and exceptional degree. -/
theorem alternating_component_models_of_orbit_models {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m)))
    (hmodels : ∀ a, ∀ E : Subgroup (alternatingOrbitImage X a),
      IsComponent (alternatingOrbitImage X a) E → AlternatingSubgroupModels m E)
    (D : Subgroup X) (hD : IsComponent X D) : AlternatingSubgroupModels m D := by
  have hcenter : ∀ a, center (D.map (alternatingOrbitProjection X a)) = ⊥ := by
    intro a
    rcases hD.map_surjective (alternatingOrbitProjection X a)
        (MulAction.toPermHom X (orbit X a)).rangeRestrict_surjective with hb | hc
    · rw [hb]
      exact (center (⊥ : Subgroup (alternatingOrbitImage X a))).eq_bot_of_subsingleton
    · let := hc.2
      let E := D.map (alternatingOrbitProjection X a)
      let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
      let : Nontrivial E := (QuotientGroup.mk'_surjective (center E)).nontrivial
      exact alternating_models_center_eq_bot (hmodels a _ hc)
  obtain ⟨a, ha, ⟨e⟩⟩ := alternating_component_equiv_orbit_image X D hD hcenter
  exact (hmodels a _ ha).of_mulEquiv e

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
