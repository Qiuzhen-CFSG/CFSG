module

public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# The two cubic orbit calculations for the local rechoice

For a nonidentity scalar a in F₄, the upper conjugate of diag(a,a⁻¹)
acts on the upper natural line by multiplication by a, and conjugates
upper(t) to upper(a²t). Both scalars cycle through the three nonzero
field elements. Matrix identities and induction prove these formulas
for powers; only the four-element scalar calculation uses finite checking.

These are the model calculations consumed on the original section and
star quotient in `ActorOrbits`. The upper conjugation parameter preserves
the chosen upper marking without requiring a new natural projection.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004, proof of
14.7.70, printed p.1073 (PDF p.1090).
-/

public section
noncomputable section
open Representation Representation.SL2FourNatural Matrix.SpecialLinearGroup

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits.Cubic
private theorem scalar_orbit (a x y : F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ n : Fin 3, a ^ (n : ℕ) * x = y := by
  have h : ∀ a x y : F, a ≠ 0 → a ≠ 1 → x ≠ 0 → y ≠ 0 →
      ∃ n : Fin 3, a ^ (n : ℕ) * x = y := by decide +kernel
  exact h a x y ha ha1 hx hy

private theorem square_ne_one (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) : a ^ 2 ≠ 1 := by
  have h : ∀ a : F, a ≠ 0 → a ≠ 1 → a ^ 2 ≠ 1 := by decide +kernel
  exact h a ha ha1

private theorem upper_mul (t s : F) : upper t * upper s = upper (t+s) := by
  apply Subtype.ext
  simp only [coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem upper_inv (t : F) : (upper t)⁻¹ = upper (-t) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  simp only [coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem diag_conjugate (a : F) (ha : a ≠ 0) (t : F) :
    diag2 a ha * upper t * (diag2 a ha)⁻¹ = upper (a^2*t) := by
  rw [diag2_inv]
  apply Subtype.ext
  simp only [coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, diag2_coe', Matrix.mul_apply, Fin.sum_univ_two, ha, pow_two, mul_comm, mul_left_comm]

private theorem cubic_conjugate (a : F) (ha : a ≠ 0) (r t : F) :
    let g := upper r * diag2 a ha * (upper r)⁻¹
    g * upper t * g⁻¹ = upper (a^2*t) := by
  dsimp
  calc
    _ = upper r * (diag2 a ha * ((upper r)⁻¹ * upper t * upper r) *
      (diag2 a ha)⁻¹) * (upper r)⁻¹ := by group
    _ = upper r * (diag2 a ha * upper t * (diag2 a ha)⁻¹) * (upper r)⁻¹ := by
      rw [upper_inv, upper_mul, upper_mul, show -r + t + r = t by ring]
    _ = upper (a^2*t) := by
      rw [diag_conjugate, upper_inv, upper_mul, upper_mul]
      congr 1
      ring

private theorem cubic_conjugate_pow (a : F) (ha : a ≠ 0) (r t : F) (n : ℕ) :
    let g := upper r * diag2 a ha * (upper r)⁻¹
    g^n * upper t * (g^n)⁻¹ = upper ((a^2)^n*t) := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_inv_rev]
    calc
      _ = (upper r * diag2 a ha * (upper r)⁻¹) *
        ((upper r * diag2 a ha * (upper r)⁻¹)^n * upper t *
        ((upper r * diag2 a ha * (upper r)⁻¹)^n)⁻¹) *
        (upper r * diag2 a ha * (upper r)⁻¹)⁻¹ := by group
      _ = _ := by rw [ih, cubic_conjugate, pow_succ' (a^2) n, mul_assoc]

private theorem cubic_axis (a : F) (ha : a ≠ 0) (r x : F) :
    action (upper r * diag2 a ha * (upper r)⁻¹) ![x, 0] = ![a*x, 0] := by
  have hu (s t : F) : action (upper s) ![t, 0] = ![t, 0] := by
    simp [upper_action]
  have hd : action (diag2 a ha) ![x, 0] = ![a*x, 0] := by
    rw [action_apply, diag2_coe']
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [map_mul, map_mul]
  change action (upper r) (action (diag2 a ha) (action ((upper r)⁻¹) ![x, 0])) = _
  rw [upper_inv, hu, hd, hu]

private theorem cubic_axis_pow (a : F) (ha : a ≠ 0) (r x : F) (n : ℕ) :
    action ((upper r * diag2 a ha * (upper r)⁻¹)^n) ![x, 0] = ![a^n*x, 0] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, LinearEquiv.mul_apply, ih, cubic_axis, pow_succ', mul_assoc]

/-- Powers of the marked cubic join any two nonzero points of the upper line. -/
theorem vector_orbit (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) (r : F)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hv1 : v 1 = 0) (hw1 : w 1 = 0) :
    ∃ n : ℕ, action ((upper r * diag2 a ha * (upper r)⁻¹)^n) v = w := by
  have he (u : V) (hu : u 1 = 0) : u = ![u 0, 0] := by
    funext i
    fin_cases i <;> simp [hu]
  have hv0 : v 0 ≠ 0 := by
    intro hz
    apply hv
    rw [he v hv1, hz]
    funext i
    fin_cases i <;> rfl
  have hw0 : w 0 ≠ 0 := by
    intro hz
    apply hw
    rw [he w hw1, hz]
    funext i
    fin_cases i <;> rfl
  obtain ⟨n, hn⟩ := scalar_orbit a (v 0) (w 0) ha ha1 hv0 hw0
  refine ⟨n, ?_⟩
  rw [he v hv1, he w hw1, cubic_axis_pow, hn]

/-- Powers of the same cubic conjugate any two nonidentity upper unipotents. -/
theorem upper_orbit (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) (r x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ n : ℕ, let g := upper r * diag2 a ha * (upper r)⁻¹
      g^n * upper x * (g^n)⁻¹ = upper y := by
  obtain ⟨n, hn⟩ := scalar_orbit (a^2) x y (pow_ne_zero _ ha) (square_ne_one a ha ha1) hx hy
  exact ⟨n, (cubic_conjugate_pow a ha r x n).trans (congrArg upper hn)⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits.Cubic
