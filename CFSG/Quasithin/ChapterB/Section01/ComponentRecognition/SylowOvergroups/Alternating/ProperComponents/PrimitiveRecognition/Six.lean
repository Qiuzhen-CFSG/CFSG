module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.Reduction
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SolvableGeneration
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# The degree-six endpoint of primitive component recognition

Conjugate a given Sylow two-subgroup to the standard Borel in A₆. The
checked six-letter overgroup classification puts every proper overgroup
in one of the two solvable parabolics. Solvability transports back along
the literal conjugation isomorphism and excludes all components. This
proves the degree-six recognition branch without needing primitivity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74, using the intrinsic six-letter parabolics of I.5,
printed pp.419–422. No SQTK or representation premise is used.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- Every proper overgroup of a Sylow two-subgroup of A₆ is solvable. -/
theorem alternating_six_proper_sylow_overgroup_solvable
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (X : Subgroup (alternatingGroup (Fin 6))) (hS : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) : Group.IsSolvable X := by
  obtain ⟨g, hg, _⟩ := a6_coatoms_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have hb : a6Borel ≤ e.symm X := by
    have hh := e.symm.monotone hS
    rwa [← hg, e.symm_apply_apply] at hh
  have hn : e.symm X ≠ ⊤ := by
    intro he
    exact hX (e.symm.injective (he.trans e.symm.map_top.symm))
  have hs : Group.IsSolvable (e.symm X) := by
    rcases a6_overgroup_borel (e.symm X) hb hn with hd | hs
    · exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hd)
    · exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hs)
  let := hs
  have hmap : e (e.symm X) = X := e.apply_symm_apply X
  let d := ((MulAut.conj g).subgroupMap (e.symm X)).trans (MulEquiv.subgroupCongr hmap)
  exact Group.isSolvable_of_surjective (f := d.toMonoidHom) d.surjective

/-- The exact nested component carrier in degree six is impossible. -/
theorem alternating_six_proper_sylow_overgroup_not_isComponent
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (X : Subgroup (alternatingGroup (Fin 6))) (hS : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) (D : Subgroup X) : ¬ IsComponent X D := by
  let := alternating_six_proper_sylow_overgroup_solvable S X hS hX
  exact not_isComponent_of_solvable D

/-- Unconditional completion of the degree-six primitive branch. -/
theorem alternating_six_primitive_component_recognition :
    AlternatingPrimitiveComponentRecognition 6 := by
  intro S X hS hX _ _ _ D hD
  exact (alternating_six_proper_sylow_overgroup_not_isComponent S X hS hX D hD).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
