module

public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace
public import Theory.AlgebraicGroup.Variety.MorphicAction

/-!
# Geometric models of Borel homogeneous spaces

A model is a reduced separated finite-type scheme with a regular action, identified
equivariantly on rational points with the actual Plücker orbit defining `G / B`.
Completeness means universal closedness of its structure morphism.

The construction from a transitive action below identifies the two homogeneous
spaces by their common stabilizer. It does not assert existence of a complete
model: that requires the closed flag orbit argument of Borel, *Linear Algebraic
Groups*, §11.1, before the fixed-point argument.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

open Variety.Geometric Bor1

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A complete geometric realization of the point-level homogeneous space `G / B`. -/
public structure CompleteModel (B : ClosedSubgroup G) where
  variety : Variety.Geometric k
  action : MorphicAction G variety
  pointEquiv : Point variety ≃ borelHomogeneousSpace B
  equivariant : ∀ (g : Variety.Point G) (x : Point variety),
    pointEquiv (action.toMulAction.smul g x) = g • pointEquiv x
  complete : IsComplete variety

/-- The identity coset gives a rational point of every model. -/
public theorem CompleteModel.nonempty {B : ClosedSubgroup G} (M : CompleteModel B) :
    Nonempty (Point M.variety) :=
  ⟨M.pointEquiv.symm (borelHomogeneousSpace.basePoint B)⟩

private theorem orbit_eq_iff_projection_eq
    (B : ClosedSubgroup G) {X : Variety.Geometric k} (A : MorphicAction G X)
    (x : Point X)
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup)
    (g h : Variety.Point G) :
    A.toMulAction.smul g x = A.toMulAction.smul h x ↔
      borelHomogeneousSpace.projection B g = borelHomogeneousSpace.projection B h := by
  let := A.toMulAction
  change ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup at hstab
  rw [borelHomogeneousSpace.projection_eq_iff]
  constructor
  · intro heq
    change g • x = h • x at heq
    have hfix : (g⁻¹ * h) • x = x := by
      rw [mul_smul, ← heq, inv_smul_smul]
    exact ⟨g⁻¹ * h, (hstab _).mp hfix, by simp⟩
  · rintro ⟨b, hb, rfl⟩
    change g • x = (g * b) • x
    rw [mul_smul, (hstab b).mpr hb]

/-- A transitive morphic action with stabilizer exactly `B` identifies its rational
points with the Plücker homogeneous space, equivariantly. -/
public theorem exists_equivariant_pointEquiv_of_transitive
    (B : ClosedSubgroup G) {X : Variety.Geometric k} (A : MorphicAction G X)
    (x : Point X)
    (htrans : ∀ y : Point X, ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup) :
    ∃ e : Point X ≃ borelHomogeneousSpace B,
      ∀ (g : Variety.Point G) (y : Point X), e (A.toMulAction.smul g y) = g • e y := by
  classical
  let := A.toMulAction
  let f : Point X → borelHomogeneousSpace B := fun y =>
    borelHomogeneousSpace.projection B (htrans y).choose
  have hf (g : Variety.Point G) : f (g • x) = borelHomogeneousSpace.projection B g := by
    exact (orbit_eq_iff_projection_eq B A x hstab _ g).mp (htrans (g • x)).choose_spec
  have hinj : Function.Injective f := by
    intro y z hyz
    obtain ⟨g, rfl⟩ := htrans y
    obtain ⟨h, rfl⟩ := htrans z
    rw [hf, hf] at hyz
    exact (orbit_eq_iff_projection_eq B A x hstab g h).mpr hyz
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := borelHomogeneousSpace.projection_surjective B y
    exact ⟨g • x, hf g⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro g y
  obtain ⟨h, rfl⟩ := htrans y
  change f (g • (h • x)) = g • f (h • x)
  rw [← mul_smul, hf, hf, borelHomogeneousSpace.projection_mul]

/-- Construct a complete model from a complete transitive geometric action with
the prescribed stabilizer. No connectedness of the acting group is required. -/
public noncomputable def CompleteModel.ofTransitive
    (B : ClosedSubgroup G) {X : Variety.Geometric k} (A : MorphicAction G X)
    (x : Point X) (hcomplete : IsComplete X)
    (htrans : ∀ y : Point X, ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup) :
    CompleteModel B :=
  let h := exists_equivariant_pointEquiv_of_transitive B A x htrans hstab
  { variety := X
    action := A
    pointEquiv := h.choose
    equivariant := h.choose_spec
    complete := hcomplete }

end Theory.AlgebraicGroup.BorelGeometricConjugacy
