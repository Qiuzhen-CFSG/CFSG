module

public import Theory.LinearAlgebra.QuadraticRankOneDisplacement

/-!
# Quadratic isometries fixing a hyperplane

For a quadratic form with nondegenerate polarization, a nonidentity isometry
with displacement rank at most one is the unique nonidentity isometry fixing
its fixed hyperplane pointwise. Write the first displacement as `f(x) d` and
the second as `f(x) e`. Polarization forces `e` to be a scalar multiple of `d`,
and preservation of the quadratic form makes that scalar zero or one.

The determinant-module application excludes rank-two offenders in the full
normalizer of the natural A₅ × A₅ tensor module (Aschbacher–Smith D.3.9).
-/

@[expose] public section

open Module
namespace QuadraticForm
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]

omit [Module.Finite F V] in
private lemma polar_of_rank_one
    (q : QuadraticForm F V) (f : Module.Dual F V) (d z : V) (hz : f z = 1)
    (h : ∀ x, q (x + f x • d) = q x) :
    ∀ x, QuadraticMap.polar q x d = -(f x * q d) := by
  have hp (x : V) : f x * (f x * q d + QuadraticMap.polar q x d) = 0 := by
    have hh := h x
    rw [QuadraticMap.map_add q, q.map_smul,
      QuadraticMap.polar_smul_right, smul_eq_mul] at hh
    linear_combination hh
  have hnonzero (x : V) (hx : f x ≠ 0) :
      QuadraticMap.polar q x d = -(f x * q d) := by
    have hh := (mul_eq_zero.mp (hp x)).resolve_left hx
    linear_combination hh
  intro x
  by_cases hx : f x = 0
  · have hh := hnonzero (x + z) (by rw [map_add, hx, hz, zero_add]; exact one_ne_zero)
    have hh' := hnonzero z (by rw [hz]; exact one_ne_zero)
    rw [map_add, hx, hz, zero_add, QuadraticMap.polar_add_left] at hh
    rw [hz] at hh'
    rw [hx]
    linear_combination hh - hh'
  · exact hnonzero x hx

/-- The pointwise stabilizer of the fixed hyperplane of a rank-one
isometry consists of that isometry and the identity. -/
theorem eq_one_or_eq_of_fixed_rank_one
    (q : QuadraticForm F V) (hq : q.polarBilin.SeparatingLeft)
    (t s : V ≃ₗ[F] V) (ht : ∀ x, q (t x) = q x) (hs : ∀ x, q (s x) = q x)
    (hr : finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1)
    (hne : t ≠ 1) (hfix : ∀ x, t x = x → s x = x) : s = 1 ∨ s = t := by
  obtain ⟨f,d,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have hform (x : V) : t x = x + f x • d := congrArg (fun l : V →ₗ[F] V => l x) he
  have hf : f ≠ 0 := by
    intro hz
    apply hne
    apply LinearEquiv.ext
    intro x
    change t x = x
    simpa only [hz, LinearMap.zero_apply, zero_smul, add_zero] using hform x
  obtain ⟨y,hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra! hh
    exact hf (LinearMap.ext hh)
  let z : V := (f y)⁻¹ • y
  have hz : f z = 1 := by simp [z, hy]
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    apply LinearEquiv.ext
    intro x
    change t x = x
    simpa only [hd, smul_zero, add_zero] using hform x
  have hqd : q d ≠ 0 := by
    intro hqd
    apply q.singular_not_mem_displacement hq t ht hr d hd hqd
    exact ⟨z, by change t z - z = d; rw [hform, hz, one_smul, add_sub_cancel_left]⟩
  let e : V := s z - z
  have hsform (x : V) : s x = x + f x • e := by
    have hx : f (x - f x • z) = 0 := by simp [hz]
    have htfix : t (x - f x • z) = x - f x • z := by
      rw [hform, hx, zero_smul, add_zero]
    have hh := hfix _ htfix
    rw [map_sub, map_smul] at hh
    calc
      s x = (x - f x • z) + f x • s z := (sub_eq_iff_eq_add).mp hh
      _ = x + f x • e := by dsimp only [e]; module
  have hpd := polar_of_rank_one q f d z hz (fun x => by rw [← hform]; exact ht x)
  have hpe := polar_of_rank_one q f e z hz (fun x => by rw [← hsform]; exact hs x)
  have hde : q d • e = q e • d := by
    have hh : q d • e - q e • d = 0 := by
      apply hq
      intro x
      change QuadraticMap.polar q (q d • e - q e • d) x = 0
      rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_comm q e x,
        QuadraticMap.polar_comm q d x, hpe, hpd]
      change q d * -(f x * q e) - q e * -(f x * q d) = 0
      ring
    exact sub_eq_zero.mp hh
  let c : F := (q d)⁻¹ * q e
  have hec : e = c • d := by
    have hh := congrArg (fun v : V => (q d)⁻¹ • v) hde
    simpa only [smul_smul, inv_mul_cancel₀ hqd, one_smul, c] using hh
  have hc : c * (c - 1) = 0 := by
    have hh := hpe z
    rw [hz, one_mul, hec, q.map_smul, QuadraticMap.polar_smul_right, hpd, hz,
      one_mul, smul_eq_mul] at hh
    apply (mul_eq_zero.mp (show c * (c - 1) * q d = 0 by linear_combination hh)).resolve_right hqd
  rcases mul_eq_zero.mp hc with hc | hc
  · left
    apply LinearEquiv.ext
    intro x
    simp only [hsform, hec, hc, zero_smul, smul_zero, add_zero]
    rfl
  · right
    have hc : c = 1 := sub_eq_zero.mp hc
    apply LinearEquiv.ext
    intro x
    rw [hsform, hec, hc, one_smul, hform]

end QuadraticForm
