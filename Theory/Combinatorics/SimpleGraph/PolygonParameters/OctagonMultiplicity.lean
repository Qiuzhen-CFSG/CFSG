module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
public import Theory.LinearAlgebra.QuadraticTrace
public import Mathlib.Tactic.LinearCombination

/-!
# Integral octagon multiplicity

The constant-vector action of the distance matrices counts the points. The
operator `s^4 I - s^3 A + s^2 D2 - s D3 + D4`, after division by
`(s+1)(s+t)(s^2+t^2)`, is a projection. Its integer trace gives the
parameter divisibility used in Fong--Seitz I (1K), printed pp.6--7.

The internal import of `DistanceMatrices` is intentional: this neighboring
counting proof uses its hidden matrix formula without exposing that body or
changing its public boundary. Consumers use the two theorems below.
-/

public noncomputable section
open LinearMap
namespace SimpleGraph.PolygonParameters

private theorem octagon_zero_multiplicity_of_recurrence
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A D₂ D₃ D₄ : Module.End ℝ V) (s t N : ℕ)
    (hs : 0 < s)
    (h₁ : A*A = ((s : ℝ)*(t+1)) • 1 + ((s : ℝ)-1) • A + D₂)
    (h₂ : A*D₂ = ((s : ℝ)*t) • A + ((s : ℝ)-1) • D₂ + D₃)
    (h₃ : A*D₃ = ((s : ℝ)*t) • D₂ + ((s : ℝ)-1) • D₃ + ((t : ℝ)+1) • D₄)
    (h₄ : A*D₄ = ((s : ℝ)*t) • D₃ + (((s : ℝ)-1)*(t+1)) • D₄)
    (htr₀ : trace ℝ V 1 = (N : ℝ))
    (htr₁ : trace ℝ V A = 0) (htr₂ : trace ℝ V D₂ = 0)
    (htr₃ : trace ℝ V D₃ = 0) (htr₄ : trace ℝ V D₄ = 0) :
    (s+1)*(s+t)*(s^2+t^2) ∣ N*s^4 := by
  let Z : Module.End ℝ V := (s:ℝ)^4 • 1 - (s:ℝ)^3 • A +
    (s:ℝ)^2 • D₂ - (s:ℝ) • D₃ + D₄
  let c : ℝ := (s+1)*(s+t)*(s^2+t^2)
  have hc : c ≠ 0 := by
    dsimp [c]
    have : (0:ℝ)<s := by exact_mod_cast hs
    positivity
  have hAZ : A*Z = (-(t+1):ℝ) • Z := by
    dsimp [Z]
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one, h₁, h₂, h₃, h₄]
    module
  have hD₂ : D₂*Z = ((t:ℝ)*(t+1)) • Z := by
    have h := congrArg (fun B : Module.End ℝ V => B*Z) h₁
    simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc, hAZ, mul_smul_comm, smul_smul] at h
    linear_combination (norm := module) -h
  have hD₃ : D₃*Z = (-((t:ℝ)^2*(t+1))) • Z := by
    have h := congrArg (fun B : Module.End ℝ V => B*Z) h₂
    simp only [add_mul, smul_mul_assoc, mul_assoc, hAZ, hD₂, mul_smul_comm, smul_smul] at h
    linear_combination (norm := module) -h
  have hD₄ : D₄*Z = (t:ℝ)^3 • Z := by
    have h := congrArg (fun B : Module.End ℝ V => B*Z) h₃
    simp only [add_mul, smul_mul_assoc, mul_assoc, hAZ, hD₂, hD₃, mul_smul_comm, smul_smul] at h
    have he : ((t:ℝ)+1) • (D₄*Z - (t:ℝ)^3 • Z) = 0 := by linear_combination (norm := module) -h
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (by positivity))
  have hZZ : Z*Z = c • Z := by
    change ((s:ℝ)^4 • 1 - (s:ℝ)^3 • A +
      (s:ℝ)^2 • D₂ - (s:ℝ) • D₃ + D₄)*Z = c • Z
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, hAZ, hD₂, hD₃, hD₄]
    dsimp [c]
    module
  let E := c⁻¹ • Z
  have hE : IsIdempotentElem E := by
    change E*E=E
    dsimp [E]
    rw [smul_mul_assoc, mul_smul_comm, hZZ, smul_smul, smul_smul]
    congr 1
    field_simp
  let n := Module.finrank ℝ (range E)
  have hn : trace ℝ V E = (n:ℝ) :=
    ((isProj_range_iff_isIdempotentElem E).mpr hE).trace
  have hZ : trace ℝ V Z = (s:ℝ)^4*N := by
    simp [Z, htr₀, htr₁, htr₂, htr₃, htr₄]
  have hh : (s:ℝ)^4*N = c*n := by
    have hh : (s:ℝ)^4*N/c = n := by simpa only [E, map_smul, smul_eq_mul, hZ, div_eq_inv_mul] using hn
    exact (div_eq_iff hc).mp hh |>.trans (mul_comm _ _)
  refine ⟨n, ?_⟩
  have hh' : (N:ℝ)*s^4 = (s+1)*(s+t)*(s^2+t^2)*n := by simpa only [c, mul_comm ((s:ℝ)^4)] using hh
  exact_mod_cast hh'

end SimpleGraph.PolygonParameters

open scoped BigOperators
namespace SimpleGraph.PolygonParameters.Datum
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {s t : ℕ}

/-- The actual point count of a finite generalized octagon. -/
theorem octagon_point_card (D : Datum G 8 s t) (hp : ∃ v, D.color v=0) :
    Fintype.card D.Point = (s+1)*(s*t+1)*(s^2*t^2+1) := by
  classical
  let A := Matrix.toLin' (D.distanceMatrix 1)
  let B := Matrix.toLin' (D.distanceMatrix 2)
  let C := Matrix.toLin' (D.distanceMatrix 3)
  let E := Matrix.toLin' (D.distanceMatrix 4)
  let v : D.Point → ℝ := fun _ => 1
  have h₁ : A*A = ((s : ℝ)*(t+1)) • 1 + ((s : ℝ)-1) • A + B := by
    have h := congrArg Matrix.toLin' D.octagon_recurrence_1
    simpa only [Matrix.toLin'_mul, map_add, map_smul, D.distanceMatrix_zero,
      Matrix.toLin'_one, Module.End.mul_eq_comp, Module.End.one_eq_id] using h
  have h₂ : A*B = ((s : ℝ)*t) • A + ((s : ℝ)-1) • B + C := by
    have h := congrArg Matrix.toLin' D.octagon_recurrence_2
    simpa only [Matrix.toLin'_mul, map_add, map_smul, Module.End.mul_eq_comp] using h
  have h₃ : A*C = ((s : ℝ)*t) • B + ((s : ℝ)-1) • C + ((t : ℝ)+1) • E := by
    have h := congrArg Matrix.toLin' D.octagon_recurrence_3
    simpa only [Matrix.toLin'_mul, map_add, map_smul, Module.End.mul_eq_comp] using h
  have hAv : A v = ((s:ℝ)*(t+1)) • v := by
    ext u
    have hdiag := congrFun (congrFun D.octagon_recurrence_1 u) u
    have hd : (D.distanceMatrix 1 * D.distanceMatrix 1) u u =
        ∑ w : D.Point, D.distanceMatrix 1 u w := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [distanceMatrix, G.dist_comm (u := w.val) (v := u.val)]
      split_ifs <;> norm_num
    rw [hd] at hdiag
    simpa [A, v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, distanceMatrix,
      Matrix.add_apply, Matrix.smul_apply] using hdiag
  have hBv : B v = ((s:ℝ)^2*t*(t+1)) • v := by
    have h := congrArg (fun F : Module.End ℝ (D.Point → ℝ) => F v) h₁
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, hAv, map_smul, smul_smul] at h
    linear_combination (norm := module) -h
  have hCv : C v = ((s:ℝ)^3*t^2*(t+1)) • v := by
    have h := congrArg (fun F : Module.End ℝ (D.Point → ℝ) => F v) h₂
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      hAv, hBv, map_smul, smul_smul] at h
    linear_combination (norm := module) -h
  have hEv : E v = ((s:ℝ)^4*t^3) • v := by
    have h := congrArg (fun F : Module.End ℝ (D.Point → ℝ) => F v) h₃
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      hAv, hBv, hCv, map_smul, smul_smul] at h
    have he : ((t:ℝ)+1) • (E v - ((s:ℝ)^4*t^3) • v) = 0 := by
      linear_combination (norm := module) -h
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (by positivity))
  have hsum : 1 + D.distanceMatrix 1 + D.distanceMatrix 2 +
      D.distanceMatrix 3 + D.distanceMatrix 4 = Matrix.of (fun (_ : D.Point) (_ : D.Point) => (1:ℝ)) := by
    rw [← D.distanceMatrix_zero]
    ext u w
    obtain ⟨d,hd⟩ := D.even_point_distance u.property w.property
    have hb := D.diameter u.val w.val
    have hdb : d≤4 := by omega
    simp only [Matrix.add_apply, Matrix.of_apply, distanceMatrix]
    interval_cases d <;> norm_num [hd]
  have hs := congrArg (fun M : Matrix D.Point D.Point ℝ => Matrix.toLin' M v) hsum
  simp only [map_add, LinearMap.add_apply, Matrix.toLin'_one] at hs
  change v + A v + B v + C v + E v = _ at hs
  rw [hAv, hBv, hCv, hEv] at hs
  obtain ⟨u,hu⟩ := hp
  have hu' := congrFun hs (⟨u,hu⟩ : D.Point)
  have hh : (Fintype.card D.Point : ℝ) = (s+1)*(s*t+1)*(s^2*t^2+1) := by
    rw [Matrix.toLin'_apply] at hu'
    simp only [Pi.add_apply, Pi.smul_apply, v, smul_eq_mul, mul_one,
      Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hu'
    nlinarith only [hu']
  exact_mod_cast hh
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {s t : ℕ}

/-- The multiplicity of the eigenvalue `-(t+1)` is a natural number. -/
theorem octagon_parameter_divisibility (D : Datum G 8 s t) (hs : 0<s)
    (hp : ∃ v, D.color v=0) :
    (s+t)*(s^2+t^2) ∣ s^4*(s*t+1)*(s^2*t^2+1) := by
  classical
  have hd : (s+1)*(s+t)*(s^2+t^2) ∣ Fintype.card D.Point*s^4 := by
    apply octagon_zero_multiplicity_of_recurrence
      (Matrix.toLin' (D.distanceMatrix 1)) (Matrix.toLin' (D.distanceMatrix 2))
      (Matrix.toLin' (D.distanceMatrix 3)) (Matrix.toLin' (D.distanceMatrix 4))
      s t (Fintype.card D.Point) hs
    · have h := congrArg Matrix.toLin' D.octagon_recurrence_1
      simpa only [Matrix.toLin'_mul, map_add, map_smul,
        D.distanceMatrix_zero, Matrix.toLin'_one, Module.End.mul_eq_comp,
        Module.End.one_eq_id] using h
    · have h := congrArg Matrix.toLin' D.octagon_recurrence_2
      simpa only [Matrix.toLin'_mul, map_add, map_smul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' D.octagon_recurrence_3
      simpa only [Matrix.toLin'_mul, map_add, map_smul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' D.octagon_recurrence_4
      simpa only [Matrix.toLin'_mul, map_add, map_smul, Module.End.mul_eq_comp] using h
    · rw [LinearMap.trace_one, Module.finrank_fintype_fun_eq_card]
    · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 1 (by decide)]
    · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 2 (by decide)]
    · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 3 (by decide)]
    · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 4 (by decide)]
  rw [D.octagon_point_card hp] at hd
  apply (Nat.mul_dvd_mul_iff_left (show 0<s+1 by omega)).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hd
end SimpleGraph.PolygonParameters
