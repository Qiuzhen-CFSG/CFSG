module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedGeometry
public import Theory.Representation.BinaryOffender.Homogeneous.TwoTypeOrbit

/-!
# Equality of two translates with the same constituent type

The subgroup intertwiner induces an intertwiner of the literal central
images. Homogeneous selection identifies those images. Full commutator
generation then lifts their equality back to the original subgroups, so
there is no remaining central error. This is the step that turns a bound
on module types into a bound on the actual Sylow orbit.

The chosen-seed consumer is in `SeedAlternativesMovedSylow`.
Source: Aschbacher--Smith A.1.42(3) and D.3.5(4), combined manuscript
of 1 March 2004, printed pp.32 and195--196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous Theory.GroupTheory.ReducedNormal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G : Type*} [Group G]

/-- Two translates of a homogeneous seed with isomorphic unchanged-actor
conjugation actions are the same actual subgroup. -/
theorem homogeneous_conjugates_eq_of_sameConjugationModule
    (H X : Subgroup G) (hXH : X ≤ H) (R : Subgroup H)
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H)))
    (hI : IsIrrPlusWith (representation H) (X.subgroupOf H) R I) (s t : R)
    (he : SameConjugationModule X
      ((subspaceImage H I).map (MulAut.conj s.val.val).toMonoidHom)
      ((subspaceImage H I).map (MulAut.conj t.val.val).toMonoidHom)) :
    (subspaceImage H I).map (MulAut.conj s.val.val).toMonoidHom =
      (subspaceImage H I).map (MulAut.conj t.val.val).toMonoidHom := by
  let ρ := representation H
  let K := X.subgroupOf H
  let c := centralTypeAction ρ K R hI.normalizes
  let S := quotientImage ρ K I hI.invariant
  have hJ (r : R) := hI.isIrrPlus.map_normalizer ρ (hI.normalizes r.property)
  have hconj (r : R) : c.conjugate r S =
      quotientImage ρ K (I.map (ρ r.val)) (hJ r).choose := by
    apply Subrepresentation.toSubmodule_injective
    rw [centralConjugate_toSubmodule]
    exact (quotientImage_map_normalizer ρ K I ⟨r.val, hI.normalizes r.property⟩).symm
  have hh : homogeneousPart S (c.span S).toSubmodule = S.toSubmodule := by
    rw [centralTypeAction_span]
    exact hI.central_homogeneous ρ
  have he' : SameConjugationModule X (subspaceImage H (I.map (ρ s.val)))
      (subspaceImage H (I.map (ρ t.val))) := by
    simpa only [ρ, subspaceImage_map] using he
  have hs := same_central_images_of_sameConjugationModule H X hXH _ _
    (hJ s).choose (hJ t).choose he'
  rw [← hconj s, ← hconj t] at hs
  have heq := c.conjugate_eq_of_sameModule S (quotientImage_irreducible ρ hI.isIrrPlus)
    hh s t hs
  rw [hconj s, hconj t] at heq
  have hmap := congrArg Subrepresentation.toSubmodule heq
  have hij : I.map (ρ s.val) = I.map (ρ t.val) := le_antisymm
    (le_of_quotientImage_le ρ (hJ s).choose_spec.1 (hJ t).choose hmap.le)
    (le_of_quotientImage_le ρ (hJ t).choose_spec.1 (hJ s).choose hmap.ge)
  simpa only [ρ, subspaceImage_map] using congrArg (subspaceImage H) hij

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

