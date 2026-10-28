module

public import Theory.LinearAlgebra.QuadraticForm.BinaryAnisotropic
public import Mathlib.RepresentationTheory.Basic

/-!
# Quadratic forms and transitivity on nonzero binary vectors

In binary dimension greater than two, an invariant quadratic form for a group
transitive on nonzero vectors is zero. Indeed, the anisotropic dimension bound
supplies a nonzero singular vector, whose orbit is every nonzero vector.
Consequently such an action cannot preserve a nonsingular quadratic form.

This provides an intrinsic alternative to the involution calculations in
Aschbacher--Smith, proof of 15.3.58, printed p.1149, for natural modules.
-/

public section

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Nonzero-vector transitivity forces every invariant quadratic form to vanish
in binary dimension greater than two. -/
theorem quadratic_eq_zero_of_nonzero_transitive
    (ρ : Representation (ZMod 2) G V) (hd : 2 < Module.finrank (ZMod 2) V)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g, ρ g x = y)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ g x, q (ρ g x) = q x) : q = 0 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have ha : ¬ q.Anisotropic := by
    intro ha
    have hh := q.finrank_le_twice_of_anisotropic_binary ha
    simp only [Module.finrank_self, mul_one] at hh
    omega
  obtain ⟨x, hx, hqx⟩ := q.not_anisotropic_iff_exists.mp ha
  ext y
  by_cases hy : y = 0
  · subst y
    simp
  · obtain ⟨g, rfl⟩ := ht x y hx hy
    simp only [zero_apply, hq, hqx]

/-- A nonsingular binary orthogonal action of dimension greater than two has
at least two orbits on nonzero vectors. -/
theorem not_nondegenerate_quadratic_of_nonzero_transitive
    (ρ : Representation (ZMod 2) G V) (hd : 2 < Module.finrank (ZMod 2) V)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g, ρ g x = y)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ g x, q (ρ g x) = q x) :
    ¬ q.polarBilin.Nondegenerate := by
  have he := quadratic_eq_zero_of_nonzero_transitive ρ hd ht q hq
  subst q
  intro hn
  have : Subsingleton V := ⟨fun x y => by
    have hx : x = 0 := hn.1 x (by intro y; simp [QuadraticMap.polar])
    have hy : y = 0 := hn.1 y (by intro x; simp [QuadraticMap.polar])
    exact hx.trans hy.symm⟩
  have hz : Module.finrank (ZMod 2) V = 0 := Module.finrank_zero_of_subsingleton
  omega

end Representation
