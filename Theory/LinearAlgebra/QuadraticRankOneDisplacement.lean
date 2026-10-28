module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Singular vectors and rank-one isometries

For a quadratic form with nondegenerate polarization, the displacement line
of an isometry contains no nonzero singular vector. Write the displacement
as `f(x) v`. If `v` were singular, preservation of the form would give
`f(x) B(x,v) = 0` for every x. Testing x and x+y forces v into the polar
radical, a contradiction. This works over every field.

The source application is the nonsingular F₄-point in Aschbacher--Smith,
combined manuscript of 1 March 2004, 14.4.6(b), printed p.1008.
-/

public section
namespace QuadraticForm

open Module
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- A rank-at-most-one isometry cannot move a nonzero singular vector. -/
theorem singular_not_mem_displacement (q : QuadraticForm F V) (hq : q.polarBilin.SeparatingLeft)
    (t : V ≃ₗ[F] V) (ht : ∀ x, q (t x) = q x)
    (hr : finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1)
    (s : V) (hs : s ≠ 0) (hqs : q s = 0) :
    s ∉ LinearMap.range (t.toLinearMap - LinearMap.id) := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have he' (x : V) : t x = x + f x • v :=
    congrArg (fun l : V →ₗ[F] V => l x) he
  rintro ⟨x, hx⟩
  have hx' : f x • v = s := by
    change t x - x = s at hx
    simpa only [he', add_sub_cancel_left] using hx
  have hfx : f x ≠ 0 := by
    intro h
    exact hs (by simpa only [h, zero_smul] using hx'.symm)
  have hqv : q v = 0 := by
    rw [← hx', q.map_smul, smul_eq_mul] at hqs
    exact (mul_eq_zero.mp hqs).resolve_left (mul_ne_zero hfx hfx)
  have hp (z : V) : f z * QuadraticMap.polar q z v = 0 := by
    have hh := ht z
    rw [he', QuadraticMap.map_add q, q.map_smul, hqv, smul_zero, add_zero,
      QuadraticMap.polar_smul_right, smul_eq_mul] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  have hpx : QuadraticMap.polar q x v = 0 :=
    (mul_eq_zero.mp (hp x)).resolve_left hfx
  have hv : v = 0 := by
    apply hq v
    intro z
    change QuadraticMap.polar q v z = 0
    rw [QuadraticMap.polar_comm]
    by_cases hfz : f z = 0
    · have hxz : f (x + z) ≠ 0 := by simpa only [map_add, hfz, add_zero] using hfx
      have hh := (mul_eq_zero.mp (hp (x + z))).resolve_left hxz
      simpa only [QuadraticMap.polar_add_left, hpx, zero_add] using hh
    · exact (mul_eq_zero.mp (hp z)).resolve_left hfz
  exact hs (by simpa only [hv, smul_zero] using hx'.symm)

section Restriction
variable {k : Type*} [Field k] [Algebra k F] [Module k V] [IsScalarTower k F V]

omit [Module.Finite F V] in
/-- Restriction of scalars multiplies the displacement rank by the field degree. -/
theorem displacement_rank_restrictScalars (t : V ≃ₗ[F] V) :
    finrank k (LinearMap.range ((t.restrictScalars k).toLinearMap - LinearMap.id)) =
      finrank k F * finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) := by
  let δ := t.toLinearMap - LinearMap.id
  change finrank k (δ.restrictScalars k).range = _
  rw [LinearMap.range_restrictScalars]
  have he := ((Submodule.restrictScalarsEquiv k F V δ.range).restrictScalars k).finrank_eq
  rw [he, ← Module.finrank_mul_finrank k F δ.range]

/-- In a degree-two extension, binary rank at most two gives the same
singular exclusion as rank at most one over the larger field. -/
theorem singular_not_mem_displacement_degree_two
    (hdegree : finrank k F = 2)
    (q : QuadraticForm F V) (hq : q.polarBilin.SeparatingLeft)
    (t : V ≃ₗ[F] V) (ht : ∀ x, q (t x) = q x)
    (hr : finrank k (LinearMap.range ((t.restrictScalars k).toLinearMap - LinearMap.id)) ≤ 2)
    (s : V) (hs : s ≠ 0) (hqs : q s = 0) :
    s ∉ LinearMap.range ((t.restrictScalars k).toLinearMap - LinearMap.id) := by
  have hdim := displacement_rank_restrictScalars (k := k) t
  rw [hdegree] at hdim
  have hsmall : finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 := by omega
  exact singular_not_mem_displacement q hq t ht hsmall s hs hqs

end Restriction
end QuadraticForm
