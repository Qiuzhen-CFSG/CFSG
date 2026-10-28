module
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A quadratic operator with nonzero rational trace

If B is supported on a rational-trace projection C and B² = dC, the
positive-root projection (C + B / √d) / 2 has integer trace. A nonzero
rational trace of B therefore expresses √d as a rational number. This
is the integrality step in the parameter-square argument for finite
thick generalized hexagons and octagons (Feit–Higman, 1964).
-/

public noncomputable section
namespace LinearMap

/-- A projected quadratic operator with nonzero rational trace forces its
positive integral square parameter to be a square in the natural numbers. -/
theorem isSquare_of_projected_quadratic_trace {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B C : Module.End ℝ V) (d : ℕ) (hd : 0 < d)
    (hCC : C * C = C) (hCB : C * B = B) (hBC : B * C = B)
    (hBB : B * B = (d : ℝ) • C)
    (a b : ℚ) (ha : a ≠ 0)
    (htrB : trace ℝ V B = (a : ℝ)) (htrC : trace ℝ V C = (b : ℝ)) :
    IsSquare d := by
  let r : ℝ := Real.sqrt d
  have hr : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr2 : r ^ 2 = d := Real.sq_sqrt (by positivity)
  let E : Module.End ℝ V := (1 / 2 : ℝ) • C + (1 / (2 * r)) • B
  have hcoefC : (1 / 2 : ℝ) * (1 / 2) +
      (1 / (2 * r)) * (1 / (2 * r)) * d = 1 / 2 := by
    field_simp
    nlinarith [hr2]
  have hcoefB : (1 / 2 : ℝ) * (1 / (2 * r)) +
      (1 / (2 * r)) * (1 / 2) = 1 / (2 * r) := by ring
  have hE : IsIdempotentElem E := by
    change E * E = E
    dsimp [E]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hCC, hCB, hBC, hBB]
    calc
      _ = ((1 / 2 : ℝ) * (1 / 2) + (1 / (2 * r)) * (1 / (2 * r)) * d) • C +
          ((1 / 2 : ℝ) * (1 / (2 * r)) + (1 / (2 * r)) * (1 / 2)) • B := by module
      _ = _ := by rw [hcoefC, hcoefB]
  let n : ℕ := Module.finrank ℝ (range E)
  have hn : trace ℝ V E = (n : ℝ) :=
    ((isProj_range_iff_isIdempotentElem E).mpr hE).trace
  have he : (1 / 2 : ℝ) * b + (1 / (2 * r)) * a = n := by
    simpa [E, htrB, htrC] using hn
  have hrel : ((2 * n : ℝ) - b) * r = a := by
    field_simp at he
    nlinarith
  have hden : (2 * (n : ℚ) - b) ≠ 0 := by
    intro hh
    have hh' : 2 * (n : ℝ) - b = 0 := by exact_mod_cast hh
    rw [hh', zero_mul] at hrel
    exact ha (by exact_mod_cast hrel.symm)
  have hrat : r = ((a / (2 * (n : ℚ) - b) : ℚ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    exact (eq_div_iff (by exact_mod_cast hden)).mpr (by simpa [mul_comm] using hrel)
  by_contra hns
  exact (irrational_sqrt_natCast_iff.mpr hns) ⟨_, hrat.symm⟩

end LinearMap

/-- Explicit projections in a quadratic ideal. -/
theorem quadratic_ideal_projections {R : Type*} [Ring R] [Algebra ℝ R]
    (Z W : R) (c e d q : ℝ)
    (hZZ : Z * Z = c • Z + e • W)
    (hZW : Z * W = (e*d) • Z + c • W)
    (hWZ : W * Z = (e*d) • Z + c • W)
    (hWW : W * W = (d*c) • Z + (d*e) • W)
    (hq : q * (c*c-e*e*d) = 1) :
    let C := (q*c) • Z - (q*e) • W
    let B := (q*c) • W - (q*e*d) • Z
    C * C = C ∧ C * B = B ∧ B * C = B ∧ B * B = d • C := by
  dsimp
  have hq2 : q*q*(c*c-e*e*d)=q := by nlinarith [congrArg (q * ·) hq]
  constructor
  · simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      hZZ, hZW, hWZ, hWW, smul_add]
    calc
      _ = (q*q*(c*c-e*e*d)) • (c • Z - e • W) := by module
      _ = _ := by rw [hq2]; module
  constructor
  · simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      hZZ, hZW, hWZ, hWW, smul_add]
    calc
      _ = (q*q*(c*c-e*e*d)) • (c • W - (e*d) • Z) := by module
      _ = _ := by rw [hq2]; module
  constructor
  · simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      hZZ, hZW, hWZ, hWW, smul_add]
    calc
      _ = (q*q*(c*c-e*e*d)) • (c • W - (e*d) • Z) := by module
      _ = _ := by rw [hq2]; module
  · simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      hZZ, hZW, hWZ, hWW, smul_add]
    calc
      _ = d • (q*q*(c*c-e*e*d)) • (c • Z - e • W) := by module
      _ = _ := by rw [hq2]; module

namespace LinearMap

/-- The two multiplication generators of a quadratic ideal suffice for the
parameter-square conclusion; only their traces need be rational. -/
theorem isSquare_of_quadratic_ideal_trace
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Z W : Module.End ℝ V) (d : ℕ) (hd : 0 < d) (c e z w : ℚ)
    (hZZ : Z * Z = (c : ℝ) • Z + (e : ℝ) • W)
    (hZW : Z * W = ((e : ℝ)*d) • Z + (c : ℝ) • W)
    (hWZ : W * Z = ((e : ℝ)*d) • Z + (c : ℝ) • W)
    (hWW : W * W = ((d : ℝ)*c) • Z + ((d : ℝ)*e) • W)
    (htrZ : trace ℝ V Z = (z : ℝ)) (htrW : trace ℝ V W = (w : ℝ))
    (hD : c*c-e*e*d ≠ 0) (hN : c*w-e*d*z ≠ 0) : IsSquare d := by
  let q : ℚ := (c*c-e*e*d)⁻¹
  have hq : (q : ℝ) * ((c : ℝ)*c-e*e*d) = 1 := by
    exact_mod_cast inv_mul_cancel₀ hD
  let C := ((q : ℝ)*c) • Z - ((q : ℝ)*e) • W
  let B := ((q : ℝ)*c) • W - ((q : ℝ)*e*d) • Z
  obtain ⟨hCC,hCB,hBC,hBB⟩ :=
    quadratic_ideal_projections Z W c e d q hZZ hZW hWZ hWW hq
  apply isSquare_of_projected_quadratic_trace B C d hd hCC hCB hBC hBB
    (q*(c*w-e*d*z)) (q*(c*z-e*w))
  · exact mul_ne_zero (inv_ne_zero hD) hN
  · simp only [B, map_sub, map_smul, smul_eq_mul, htrZ, htrW]
    push_cast
    ring
  · simp only [C, map_sub, map_smul, smul_eq_mul, htrZ, htrW]
    push_cast
    ring

end LinearMap

namespace LinearMap

/-- A quadratic annihilator on one invariant ideal gives the square
constraint as soon as its two rational traces do not cancel. -/
theorem isSquare_of_quadratic_annihilator_trace
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Y Z : Module.End ℝ V) (d : ℕ) (hd : 0 < d) (c e z w : ℚ)
    (hYZ : Y * Z = Z * Y)
    (hquad : Y * (Y * Z) = (d : ℝ) • Z)
    (hZZ : Z * Z = (c : ℝ) • Z + (e : ℝ) • (Y * Z))
    (htrZ : trace ℝ V Z = (z : ℝ)) (htrW : trace ℝ V (Y * Z) = (w : ℝ))
    (hD : c*c-e*e*d ≠ 0) (hN : c*w-e*d*z ≠ 0) : IsSquare d := by
  have hWZ : (Y * Z) * Z = ((e : ℝ)*d) • Z + (c : ℝ) • (Y * Z) := by
    rw [mul_assoc, hZZ, mul_add, mul_smul_comm, mul_smul_comm, hquad]
    module
  have hZW : Z * (Y * Z) = ((e : ℝ)*d) • Z + (c : ℝ) • (Y * Z) := by
    rw [← mul_assoc, ← hYZ]
    exact hWZ
  have hWW : (Y * Z) * (Y * Z) =
      ((d : ℝ)*c) • Z + ((d : ℝ)*e) • (Y * Z) := by
    rw [mul_assoc, hZW, mul_add, mul_smul_comm, mul_smul_comm, hquad]
    module
  exact isSquare_of_quadratic_ideal_trace Z (Y*Z) d hd c e z w
    hZZ hZW hWZ hWW htrZ htrW hD hN

end LinearMap
