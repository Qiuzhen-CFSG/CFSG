module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Projective intertwiners preserve symplectic orthogonality

An intertwiner for an automorphism of the actual symplectic matrix group
identifies point-stabilizer orbits. The punctured perpendicular space has
`q² + q` points and the nonorthogonal orbit has `q³` points. These sizes differ
for every finite field, including `q = 2`, so the two orbits cannot be exchanged.

We reuse the characteristic-independent geometry already proved in
`PSp4Three.ProjectiveGeometry`. Despite that module's application-specific name,
its orbit and counting results are generic. Its rank-two matrix carrier, vector
action, and form are definitionally the same as this module's; the equivalence
between its representative-vector orthogonality and our subspace orthogonality
is proved explicitly below. The quotient projection is surjective, so its
projective-group stabilizer orbits are exactly the matrix-group orbits.

The reused geometry is the CFSG adaptation of Gerald Höhn and the ATLAS
contributors' `Symplectic/{PointGeometry,PointOrbits,PointCount,OrthogonalFrame}`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, covered by the ATLAS Research
and Attribution License 1.0; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. This module adds orbit transport and the finite
suborbit-size distinction, without any automorphism-classification premise.

This is the geometric helper for the automorphism fact used in
Aschbacher--Smith F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
-/

public noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization
variable {F : Type*} [Field F]

private theorem orthogonal_port_iff (p q : ProjectivePoint F) :
    Orthogonal p q ↔ Matrix.PSp4Three.Orthogonal p q := by
  rw [← mk_rep p, ← mk_rep q, orthogonal_mk_iff, Matrix.PSp4Three.orthogonal_mk]
  rfl

private theorem same_suborbit_iff (p x y : ProjectivePoint F) :
    Matrix.PSp4Three.suborbitIndex p x = Matrix.PSp4Three.suborbitIndex p y ↔
      ∃ g : Sp F, g • p = p ∧ g • x = y := by
  constructor
  · intro h
    obtain ⟨⟨g, hgp⟩, hgx⟩ := Matrix.PSp4Three.suborbitIndex_transitive (by decide) p x y h
    obtain ⟨g, rfl⟩ := Matrix.PSp4Three.projection_surjective g
    exact ⟨g, hgp, hgx⟩
  · rintro ⟨g, hgp, rfl⟩
    exact (Matrix.PSp4Three.suborbitIndex_invariant p x
      ⟨Matrix.PSp4Three.projection g, hgp⟩).symm

private theorem intertwining_suborbit_iff (a : MulAut (Sp F))
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ (g : Sp F) (p : ProjectivePoint F), φ (g • p) = a g • φ p)
    (p x y : ProjectivePoint F) :
    Matrix.PSp4Three.suborbitIndex p x = Matrix.PSp4Three.suborbitIndex p y ↔
      Matrix.PSp4Three.suborbitIndex (φ p) (φ x) =
        Matrix.PSp4Three.suborbitIndex (φ p) (φ y) := by
  rw [same_suborbit_iff, same_suborbit_iff]
  constructor
  · rintro ⟨g, hgp, hgx⟩
    exact ⟨a g, by rw [← hφ, hgp], by rw [← hφ, hgx]⟩
  · rintro ⟨g, hgp, hgx⟩
    refine ⟨a.symm g, φ.injective ?_, φ.injective ?_⟩ <;>
      rw [hφ, a.apply_symm_apply]
    · exact hgp
    · exact hgx

private theorem intertwining_card_suborbit (a : MulAut (Sp F))
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ (g : Sp F) (p : ProjectivePoint F), φ (g • p) = a g • φ p)
    (p x : ProjectivePoint F) :
    Nat.card {y : ProjectivePoint F //
      Matrix.PSp4Three.suborbitIndex p y = Matrix.PSp4Three.suborbitIndex p x} =
    Nat.card {y : ProjectivePoint F //
      Matrix.PSp4Three.suborbitIndex (φ p) y = Matrix.PSp4Three.suborbitIndex (φ p) (φ x)} :=
  Nat.card_congr (φ.subtypeEquiv (fun y => intertwining_suborbit_iff a φ hφ p y x))

private theorem field_card_ge_two [Finite F] : 2 ≤ Nat.card F := by
  have h : 1 < Nat.card F := Finite.one_lt_card
  omega

private theorem card_perp [Finite F] (p : ProjectivePoint F) :
    Nat.card {q : ProjectivePoint F // Matrix.PSp4Three.Orthogonal p q} =
      Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [Matrix.PSp4Three.card_perpendicular_points]
  norm_num only
  rw [← Nat.geomSum_eq field_card_ge_two]
  simp [Finset.sum_range_succ]
  ring

private theorem card_points [Finite F] : Nat.card (ProjectivePoint F) =
    Nat.card F ^ 3 + Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [Matrix.PSp4Three.card_points]
  norm_num only
  rw [← Nat.geomSum_eq field_card_ge_two]
  simp [Finset.sum_range_succ]
  ring

private theorem card_suborbit_one [Finite F] (p : ProjectivePoint F) :
    Nat.card {q : ProjectivePoint F // Matrix.PSp4Three.suborbitIndex p q = 1} =
      Nat.card F ^ 2 + Nat.card F := by
  rw [Matrix.PSp4Three.card_suborbit_one, card_perp, Nat.add_sub_cancel]

private theorem card_suborbit_two [Finite F] (p : ProjectivePoint F) :
    Nat.card {q : ProjectivePoint F // Matrix.PSp4Three.suborbitIndex p q = 2} =
      Nat.card F ^ 3 := by
  rw [Matrix.PSp4Three.card_suborbit_two, card_points, card_perp]
  omega

private theorem suborbit_sizes_ne [Finite F] :
    Nat.card F ^ 2 + Nat.card F ≠ Nat.card F ^ 3 := by
  have hq := field_card_ge_two (F := F)
  have hsq : 2 * Nat.card F ≤ Nat.card F ^ 2 := by nlinarith
  have hcube : 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 3 := by nlinarith
  omega

/-- A projective permutation intertwining an automorphism preserves the actual
symplectic orthogonality relation, including over the two-element field. -/
theorem orthogonal_iff_of_projective_intertwining [Finite F] [CharP F 2]
    (a : MulAut (Sp F)) (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ (g : Sp F) (p : ProjectivePoint F), φ (g • p) = a g • φ p)
    (p q : ProjectivePoint F) : Orthogonal (φ p) (φ q) ↔ Orthogonal p q := by
  rw [orthogonal_port_iff, orthogonal_port_iff]
  by_cases he : q = p
  · subst q
    simp only [Matrix.PSp4Three.orthogonal_self]
  have he' : φ q ≠ φ p := fun h => he (φ.injective h)
  have hc := intertwining_card_suborbit a φ hφ p q
  have hne := suborbit_sizes_ne (F := F)
  by_cases ho : Matrix.PSp4Three.Orthogonal p q <;>
    by_cases ho' : Matrix.PSp4Three.Orthogonal (φ p) (φ q)
  · exact iff_of_true ho' ho
  · have hi := (Matrix.PSp4Three.suborbitIndex_eq_one_iff p q).mpr ⟨ho, he⟩
    have hi' := (Matrix.PSp4Three.suborbitIndex_eq_two_iff (φ p) (φ q)).mpr ho'
    rw [hi, hi', card_suborbit_one, card_suborbit_two] at hc
    exact (hne hc).elim
  · have hi := (Matrix.PSp4Three.suborbitIndex_eq_two_iff p q).mpr ho
    have hi' := (Matrix.PSp4Three.suborbitIndex_eq_one_iff (φ p) (φ q)).mpr ⟨ho', he'⟩
    rw [hi, hi', card_suborbit_two, card_suborbit_one] at hc
    exact (hne hc.symm).elim
  · exact iff_of_false ho' ho

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
