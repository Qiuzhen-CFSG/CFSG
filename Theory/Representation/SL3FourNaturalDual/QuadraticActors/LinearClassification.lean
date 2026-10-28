module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.PlaneCases
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.Placement
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.Transport

/-!
# Internal quadratic actors on the SL₃(4) natural-plus-dual module

A nontrivial quadratic actor has a common natural image line or a common
fixed hyperplane. Arbitrary GL₃ conjugation, and inverse transpose for the
second orientation, place it in a literal root plane with equivariant
coordinates on both summands. Its binary parameter space has fixed
codimension twice one plus the dimension of its F₄-span. The prescribed
small-codimension inequality forces either a full root group of rank two
and codimension four, or a parameter plane of rank three or four and
codimension six. Simultaneous parameter coordinates supply the actual
root markings, which are then transported back to the original actor.

This proves the internal matrix classification; containment of an ambient
actor in the specified SL₃(4) component is the separate ambient reduction.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors
open BinaryOffender LinearClassification

/-- The internal SL₃(4) quadratic-actor classification, with exact numerical
alternatives and genuine equivariant root markings. -/
theorem criticalShapes_internal (A : Subgroup SL) (hA : IsElementaryTwo A)
    (hq : IsQuadratic representation A)
    (hsmall : fixedCodim representation A ≤ 2 * rank A) (hrank : rank A ≤ 4) :
    CriticalShapes representation A := by
  obtain ⟨f, E, D, hE, hD⟩ := exists_rootPlane_coordinates A hA.1 hq
  have hn : D ≠ ⊥ := (planeActor_ne_bot D).mp (by
    rw [← hD]
    intro h
    apply hA.1
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    simpa only [Subgroup.map_bot] using h)
  have hr : rank (planeActor D) = rank A := by
    rw [← hD]
    exact rank_map_injective f.toMonoidHom f.injective A
  have hc : fixedCodim representation (planeActor D) = fixedCodim representation A := by
    rw [← hD]
    exact (fixedCodim_map_equivariant representation representation f.toMonoidHom E hE A).symm
  have hshape := criticalShapes_planeActor D hn (by rwa [hc, hr]) (by rwa [hr])
  have he : ∀ g v, E (representation (f.symm.toMonoidHom g) v) = representation g (E v) := by
    intro g v
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hE (f.symm g) v
  have hback : (planeActor D).map f.symm.toMonoidHom = A := by
    rw [← hD, Subgroup.map_map]
    have hf : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id SL := by
      apply MonoidHom.ext
      intro g
      exact f.symm_apply_apply g
    rw [hf, Subgroup.map_id]
  have h := criticalShapes_map representation f.symm.toMonoidHom f.symm.injective E he _ hshape
  rwa [hback] at h

end Representation.SL3FourNaturalDual.QuadraticActors
