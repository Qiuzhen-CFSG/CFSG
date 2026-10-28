module

public import Theory.SpecificGroups.OrthogonalFourBinary.SingularOrbit
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Transporting the binary orthogonal action to a subgroup

A natural-action witness supplies actual coordinates on `V`, a surjective
homomorphism from `M` to the isometry group, and compatibility with ambient
conjugation. Thus it asserts the full natural orthogonal action, not just
an abstract group isomorphism. The coordinate orbit theorem then yields
conjugators in `M` between any two nonidentity singular vectors of `V`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2(1) and the orthogonal-space description on pp.1121–1122;
application to 15.3.62(2) on p.1151.
-/

@[expose] public section
namespace OrthogonalFourBinary
open Subgroup Theory.AlgebraicGroup
open scoped IsMulCommutative


variable {G : Type*} [Group G] (V M : Subgroup G)

/-- The full isometry group acting on the specified subgroup by conjugation. -/
structure NaturalAction where
  coordinates : V ≃* Multiplicative Space
  action : M →* quadraticIsometrySubgroup (k := F) (V := Space) form
  onto : Function.Surjective action
  intertwines : ∀ (m : M) (v : V),
    (coordinates.symm (Multiplicative.ofAdd
      ((action m).val (Multiplicative.toAdd (coordinates v)))) : G) =
      MulAut.conj (m : G) (v : G)

variable {V M}

/-- Compatibility makes the ambient subgroup normalize the module. -/
theorem NaturalAction.normalizes (d : NaturalAction V M) : M ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro m hm v hv
  rw [← show MulAut.conj m v = m * v * m⁻¹ from rfl, ← d.intertwines ⟨m, hm⟩ ⟨v, hv⟩]
  exact Subtype.property _

/-- Singularity for the transported quadratic form. -/
def NaturalAction.singular (d : NaturalAction V M) (v : V) : Prop :=
  form (Multiplicative.toAdd (d.coordinates v)) = 0

/-- Singular-vector transitivity lifted through the actual action homomorphism. -/
theorem NaturalAction.exists_conjugator_of_singular (d : NaturalAction V M)
    (x y : V) (hx : x ≠ 1) (hy : y ≠ 1) (hxs : d.singular x) (hys : d.singular y) :
    ∃ m ∈ M, MulAut.conj m (x : G) = (y : G) := by
  have hne (v : V) (hv : v ≠ 1) : Multiplicative.toAdd (d.coordinates v) ≠ 0 := by
    change d.coordinates v ≠ 1
    intro h
    exact hv (d.coordinates.injective (h.trans (map_one d.coordinates).symm))
  obtain ⟨e, he⟩ := exists_isometry_of_singular _ _ (hne x hx) (hne y hy) hxs hys
  obtain ⟨m, hm⟩ := d.onto ⟨e.toLinearEquiv, (mem_quadraticIsometrySubgroup form e.toLinearEquiv).mpr e.map_app'⟩
  refine ⟨m, m.property, ?_⟩
  rw [← d.intertwines m x, hm]
  change (d.coordinates.symm (Multiplicative.ofAdd (e (Multiplicative.toAdd
    (d.coordinates x)))) : G) = y
  rw [he]
  exact congrArg Subtype.val (d.coordinates.symm_apply_apply y)

end OrthogonalFourBinary
