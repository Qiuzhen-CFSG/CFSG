module
public import Theory.LinearAlgebra.QuadraticTrace
public import Mathlib.Tactic.NoncommRing

/-!
# Square constraints from the polygon distance operators

For a finite thick hexagon or octagon, the distance operators obey a three-
or four-step recurrence. An explicit quadratic ideal in their algebra has
rational traces, and its projected positive-root operator has integer trace.
This forces the parameter product (or twice the product) to be a square.
The geometric application constructs all the distance recurrences.

Source: Feit--Higman, The nonexistence of certain generalized polygons,
J. Algebra 1 (1964), Theorems 1--2; used in Fong--Seitz I (1J).
-/

public noncomputable section
open LinearMap

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters

theorem hexagon_square_of_recurrence
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A D₂ D₃ : Module.End ℝ V) (s t N : ℕ)
    (hs : 1 < s) (ht : 1 < t) (hN : 0 < N)
    (h₁ : A*A = ((s : ℝ)*(t+1)) • 1 + ((s : ℝ)-1) • A + D₂)
    (h₂ : A*D₂ = ((s : ℝ)*t) • A + ((s : ℝ)-1) • D₂ + ((t : ℝ)+1) • D₃)
    (h₃ : A*D₃ = ((s : ℝ)*t) • D₂ + (((s : ℝ)-1)*(t+1)) • D₃)
    (htr₀ : trace ℝ V 1 = (N : ℝ))
    (htr₁ : trace ℝ V A = 0) (htr₂ : trace ℝ V D₂ = 0)
    (htr₃ : trace ℝ V D₃ = 0) : IsSquare (s*t) := by
  let Y : Module.End ℝ V := A - ((s : ℝ)-1) • 1
  let Z : Module.End ℝ V := Y*Y + ((s+t-s*t-1 : ℝ)) • Y -
    (((s : ℝ)*t+1)*(s+t)) • 1
  have hYA : Y*A = ((s : ℝ)*(t+1)) • 1 + D₂ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₁]
    module
  have hY₂ : Y*D₂ = ((s : ℝ)*t) • A + ((t : ℝ)+1) • D₃ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₂]
    module
  have hY₃ : Y*D₃ = ((s : ℝ)*t) • D₂ + (((s : ℝ)-1)*t) • D₃ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₃]
    module
  have hZ : Z = D₂ - ((t : ℝ)*(s-1)) • A - ((s : ℝ)*t*(t+1)) • 1 := by
    dsimp [Z]
    rw [show Y*Y = Y*A - ((s : ℝ)-1) • Y by
      dsimp [Y]; simp only [mul_sub, mul_smul_comm, mul_one]]
    rw [hYA]
    dsimp [Y]
    module
  have hW : Y*Z = ((t : ℝ)+1) • D₃ - ((t : ℝ)*(s-1)) • D₂ -
      ((s : ℝ)*t*t) • A := by
    rw [hZ, mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, hY₂, hYA]
    dsimp [Y]
    module
  have hquad : Y*(Y*Z) = ((s*t : ℕ) : ℝ) • Z := by
    rw [hW, mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      hY₃, hY₂, hYA, hZ]
    push_cast
    module
  have hYZ : Y*Z = Z*Y := by
    dsimp [Z]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm,
      smul_mul_assoc, one_mul, mul_one, mul_assoc]
  have hZZ : Z*Z = (((s : ℝ)*t-((s : ℝ)*t+1)*(s+t))) • Z +
      ((s+t-s*t-1 : ℝ)) • (Y*Z) := by
    calc
      Z*Z = (Y*Y + ((s+t-s*t-1 : ℝ)) • Y -
          (((s : ℝ)*t+1)*(s+t)) • 1) * Z := by rfl
      _ = _ := by
        rw [sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
          mul_assoc, hquad]
        push_cast
        module
  have hz : trace ℝ V Z = (-((s : ℚ)*t*(t+1)*N) : ℚ) := by
    rw [hZ]
    simp only [map_sub, map_smul, smul_eq_mul, htr₀, htr₁, htr₂, mul_zero, sub_zero]
    push_cast
    ring
  have hw : trace ℝ V (Y*Z) = ((0 : ℚ) : ℝ) := by
    rw [hW]
    simp [htr₁, htr₂, htr₃]
  apply isSquare_of_quadratic_annihilator_trace Y Z (s*t)
    (Nat.mul_pos (by omega) (by omega))
    ((s : ℚ)*t-((s : ℚ)*t+1)*(s+t)) ((s+t-s*t-1 : ℚ))
    (-((s : ℚ)*t*(t+1)*N)) 0 hYZ hquad
  · convert hZZ using 1
    push_cast
    rfl
  · exact hz
  · exact hw
  · have hs0 : (0 : ℚ) < s := by exact_mod_cast (by omega : 0 < s)
    have ht0 : (0 : ℚ) < t := by exact_mod_cast (by omega : 0 < t)
    have he : (((s : ℚ)*t-(s*t+1)*(s+t))*((s : ℚ)*t-(s*t+1)*(s+t))-
        (s+t-s*t-1)*(s+t-s*t-1)*(s*t)) =
        (s^2+s*t+t^2)*(s^2*t^2+s*t+1) := by ring
    push_cast
    rw [he]
    positivity
  · have hs1 : (1 : ℚ) < s := by exact_mod_cast hs
    have ht1 : (1 : ℚ) < t := by exact_mod_cast ht
    have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
    have he : (((s : ℚ)*t-(s*t+1)*(s+t))*0-
        (s+t-s*t-1)*(s*t)*(-(s*t*(t+1)*N))) =
        -(s^2*t^2*(s-1)*(t-1)*(t+1)*N) := by ring
    push_cast
    rw [he]
    exact neg_ne_zero.mpr (ne_of_gt (by positivity))


theorem octagon_square_of_recurrence
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A D₂ D₃ D₄ : Module.End ℝ V) (s t N : ℕ)
    (hs : 1 < s) (ht : 1 < t) (hN : 0 < N)
    (h₁ : A*A = ((s : ℝ)*(t+1)) • 1 + ((s : ℝ)-1) • A + D₂)
    (h₂ : A*D₂ = ((s : ℝ)*t) • A + ((s : ℝ)-1) • D₂ + D₃)
    (h₃ : A*D₃ = ((s : ℝ)*t) • D₂ + ((s : ℝ)-1) • D₃ + ((t : ℝ)+1) • D₄)
    (h₄ : A*D₄ = ((s : ℝ)*t) • D₃ + (((s : ℝ)-1)*(t+1)) • D₄)
    (htr₀ : trace ℝ V 1 = (N : ℝ))
    (htr₁ : trace ℝ V A = 0) (htr₂ : trace ℝ V D₂ = 0)
    (htr₃ : trace ℝ V D₃ = 0) (htr₄ : trace ℝ V D₄ = 0) : IsSquare (2*s*t) := by
  let Y : Module.End ℝ V := A - ((s : ℝ)-1) • 1
  let H : Module.End ℝ V := Y*Y + ((s+t-s*t-1 : ℝ)) • Y -
    (((s : ℝ)*t+1)*(s+t)) • 1
  let Z := Y*H
  have hYA : Y*A = ((s : ℝ)*(t+1)) • 1 + D₂ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₁]
    module
  have hY₂ : Y*D₂ = ((s : ℝ)*t) • A + D₃ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₂]
    module
  have hY₃ : Y*D₃ = ((s : ℝ)*t) • D₂ + ((t : ℝ)+1) • D₄ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₃]
    module
  have hY₄ : Y*D₄ = ((s : ℝ)*t) • D₃ + (((s : ℝ)-1)*t) • D₄ := by
    dsimp [Y]
    rw [sub_mul, smul_mul_assoc, one_mul, h₄]
    module
  have hH : H = D₂ - ((t : ℝ)*(s-1)) • A - ((s : ℝ)*t*(t+1)) • 1 := by
    dsimp [H]
    rw [show Y*Y = Y*A - ((s : ℝ)-1) • Y by
      dsimp [Y]; simp only [mul_sub, mul_smul_comm, mul_one]]
    rw [hYA]
    dsimp [Y]
    module
  have hZ : Z = D₃ - ((t : ℝ)*(s-1)) • D₂ - ((s : ℝ)*t*t) • A := by
    change Y*H = _
    rw [hH, mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, hY₂, hYA]
    dsimp [Y]
    module
  have hW : Y*Z = ((t : ℝ)+1) • D₄ - ((t : ℝ)*(s-1)) • D₃ +
      ((s : ℝ)*t*(1-t)) • D₂ - ((s : ℝ)*t*t*(s-1)) • A -
      ((s : ℝ)^2*t^2*(t+1)) • 1 := by
    rw [hZ, mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, hY₃, hY₂, hYA]
    module
  have hquad : Y*(Y*Z) = ((2*s*t : ℕ) : ℝ) • Z := by
    rw [hW]
    simp only [mul_sub, mul_add, mul_smul_comm, mul_one, hY₄, hY₃, hY₂, hYA]
    rw [hZ]
    dsimp [Y]
    push_cast
    module
  have hYZ : Y*Z = Z*Y := by
    dsimp [Z, H]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm,
      smul_mul_assoc, one_mul, mul_one, mul_assoc]
  have hZZ : Z*Z = ((s+t-s*t-1 : ℝ)*(2*s*t)) • Z +
      (((2*s*t : ℝ)-((s : ℝ)*t+1)*(s+t))) • (Y*Z) := by
    calc
      Z*Z = (Y*(Y*Y + ((s+t-s*t-1 : ℝ)) • Y -
          (((s : ℝ)*t+1)*(s+t)) • 1)) * Z := by rfl
      _ = _ := by
        simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm,
          smul_mul_assoc, one_mul, mul_one, mul_assoc, hquad]
        push_cast
        module
  have hz : trace ℝ V Z = ((0 : ℚ) : ℝ) := by
    rw [hZ]
    simp [htr₁, htr₂, htr₃]
  have hw : trace ℝ V (Y*Z) = (-((s : ℚ)^2*t^2*(t+1)*N) : ℚ) := by
    rw [hW]
    simp only [map_sub, map_add, map_smul, smul_eq_mul, htr₀,
      htr₁, htr₂, htr₃, htr₄, mul_zero, zero_add, zero_sub, sub_zero]
    push_cast
    ring
  apply isSquare_of_quadratic_annihilator_trace Y Z (2*s*t)
    (by positivity)
    ((s+t-s*t-1 : ℚ)*(2*s*t)) (((2*s*t : ℚ)-(s*t+1)*(s+t)))
    0 (-((s : ℚ)^2*t^2*(t+1)*N)) hYZ hquad
  · convert hZZ using 1
    push_cast
    rfl
  · exact hz
  · exact hw
  · have hs0 : (0 : ℚ) < s := by exact_mod_cast (by omega : 0 < s)
    have ht0 : (0 : ℚ) < t := by exact_mod_cast (by omega : 0 < t)
    have he : ((s+t-s*t-1 : ℚ)*(2*s*t))*((s+t-s*t-1)*(2*s*t))-
        (2*s*t-(s*t+1)*(s+t))*(2*s*t-(s*t+1)*(s+t))*(2*s*t) =
        -(2*s*t*(s^2+t^2)*(s^2*t^2+1)) := by ring
    push_cast
    rw [he]
    exact neg_ne_zero.mpr (ne_of_gt (by positivity))
  · have hs1 : (1 : ℚ) < s := by exact_mod_cast hs
    have ht1 : (1 : ℚ) < t := by exact_mod_cast ht
    have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
    have he : ((s+t-s*t-1 : ℚ)*(2*s*t))*(-(s^2*t^2*(t+1)*N))-
        (2*s*t-(s*t+1)*(s+t))*(2*s*t)*0 =
        2*s^3*t^3*(s-1)*(t-1)*(t+1)*N := by ring
    push_cast
    rw [he]
    exact ne_of_gt (by positivity)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
