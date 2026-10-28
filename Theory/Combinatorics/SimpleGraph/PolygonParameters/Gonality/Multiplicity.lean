module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Odd
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Polynomial.FieldDivision
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Odd

/-!
# Integral spectral multiplicities from the polygon recurrences

If `(X-r)*p` annihilates an operator and `p(r)` is nonzero, then
`p(A)/p(r)` is a projection. Its trace is its natural-number rank.
For the polygon operator, traces of divided distance polynomials satisfy
the homogeneous Chebyshev recurrence: the additional distance matrix has
zero trace. This computes the numerator of each simple-root multiplicity
for both odd and even gonality, on the literal point adjacency matrix.

This is the projection-trace method cited as Feit--Higman Lemma 3.4 in
Fong--Seitz I, printed p.6. Source: Feit--Higman, J. Algebra 1 (1964),
114--131, DOI 10.1016/0021-8693(64)90028-6. The integrality statements below
are proved from the metric datum. They do not by themselves exclude the
remaining gonalities; their polynomial and arithmetic consequences remain
separate obligations.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

/-- A simple linear factor of an annihilating polynomial gives a spectral
projection, whose trace is a natural number. -/
theorem exists_nat_trace_of_linear_factor {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (A : Module.End ℝ V)
    (r : ℝ) (p : ℝ[X]) (hp : p.eval r≠0)
    (hzero : aeval A ((X-C r)*p)=0) :
    ∃ n : ℕ, LinearMap.trace ℝ V (aeval A p) = p.eval r*n := by
  let B : Module.End ℝ V := aeval A p
  obtain ⟨q,hq⟩ := X_sub_C_dvd_sub_C_eval (p:=p) (a:=r)
  have he : p*p-C (p.eval r)*p = ((X-C r)*p)*q := by
    calc
      _ = (p-C (p.eval r))*p := by ring
      _ = ((X-C r)*q)*p := by rw [hq]
      _ = _ := by ring
  have he' := congrArg (aeval A) he
  simp only [map_sub,map_mul,aeval_C,hzero,zero_mul,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at he'
  have hBB : B*B=p.eval r • B := sub_eq_zero.mp he'
  let E : Module.End ℝ V := (p.eval r)⁻¹ • B
  have hE : IsIdempotentElem E := by
    change E*E=E
    dsimp [E]
    rw [smul_mul_assoc,mul_smul_comm,hBB,smul_smul,smul_smul]
    congr 1
    field_simp
  refine ⟨Module.finrank ℝ (LinearMap.range E),?_⟩
  have ht := ((LinearMap.isProj_range_iff_isIdempotentElem E).mpr hE).trace
  have hb : B=p.eval r • E := by simp [E,smul_smul,hp]
  change LinearMap.trace ℝ V B=_
  rw [hb,map_smul,ht,smul_eq_mul]

/-- The matrix version, retaining the literal adjacency matrix. -/
theorem exists_nat_matrix_trace_of_linear_factor {I : Type*} [Fintype I]
    [DecidableEq I] (A : Matrix I I ℝ) (r : ℝ) (p : ℝ[X]) (hp : p.eval r≠0)
    (hzero : aeval A ((X-C r)*p)=0) :
    ∃ n : ℕ, (aeval A p).trace=p.eval r*n := by
  have he (f : ℝ[X]) : Matrix.toLin' (aeval A f) = aeval (Matrix.toLin' A) f := by
    exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv'.toAlgHom) A f).symm
  have hz := congrArg Matrix.toLin' hzero
  rw [he,map_zero] at hz
  obtain ⟨n,hn⟩ := exists_nat_trace_of_linear_factor (Matrix.toLin' A) r p hp hz
  refine ⟨n,?_⟩
  rw [←he,Matrix.trace_toLin'_eq] at hn
  exact hn
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

/-- Polynomial division by `X-r`, including the constant remainder. -/
def dividedPolynomial (p : ℝ[X]) (r : ℝ) : ℝ[X] := p /ₘ (X-C r)

theorem mul_dividedPolynomial (p : ℝ[X]) (r : ℝ) :
    (X-C r)*dividedPolynomial p r=p-C (p.eval r) := by
  simp only [dividedPolynomial,X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    modByMonic_X_sub_C_eq_C_eval]

@[simp] theorem dividedPolynomial_C (c r : ℝ) : dividedPolynomial (C c) r=0 := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero r)
  simp [mul_dividedPolynomial]

@[simp] theorem dividedPolynomial_X (r : ℝ) : dividedPolynomial X r=1 := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero r)
  simp [mul_dividedPolynomial]

@[simp] theorem dividedPolynomial_sub (p q : ℝ[X]) (r : ℝ) :
    dividedPolynomial (p-q) r=dividedPolynomial p r-dividedPolynomial q r := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero r)
  rw [mul_dividedPolynomial,mul_sub,mul_dividedPolynomial,mul_dividedPolynomial]
  simp only [eval_sub,map_sub]
  ring

@[simp] theorem dividedPolynomial_C_mul (c : ℝ) (p : ℝ[X]) (r : ℝ) :
    dividedPolynomial (C c*p) r=C c*dividedPolynomial p r := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero r)
  rw [mul_dividedPolynomial,mul_left_comm,mul_dividedPolynomial]
  simp only [eval_mul,eval_C,map_mul]
  ring

theorem dividedPolynomial_recurrence (p q : ℝ[X]) (a b r : ℝ) :
    dividedPolynomial ((X-C a)*p-C b*q) r =
      p+C (r-a)*dividedPolynomial p r-C b*dividedPolynomial q r := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero r)
  rw [mul_dividedPolynomial,mul_sub,mul_add,
    mul_left_comm (X-C r) (C (r-a)),mul_left_comm (X-C r) (C b),
    mul_dividedPolynomial,mul_dividedPolynomial]
  simp only [eval_sub,eval_mul,eval_X,eval_C,map_sub,map_mul]
  ring

theorem dividedPolynomial_eval (p : ℝ[X]) (r : ℝ) :
    (dividedPolynomial p r).eval r=p.derivative.eval r := by
  have he := congrArg (Polynomial.eval r)
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p r)
  simpa [dividedPolynomial] using he

/-- The quotient at a simple root has the integral trace prescribed by its derivative. -/
theorem exists_nat_matrix_trace_dividedPolynomial {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (p : ℝ[X]) (r : ℝ) (hr : p.eval r=0)
    (hd : p.derivative.eval r≠0) (hz : aeval A p=0) :
    ∃ n : ℕ, (aeval A (dividedPolynomial p r)).trace=p.derivative.eval r*n := by
  have he : (X-C r)*dividedPolynomial p r=p := by simp [mul_dividedPolynomial,hr]
  obtain ⟨n,hn⟩ := exists_nat_matrix_trace_of_linear_factor A r (dividedPolynomial p r)
    (by rwa [dividedPolynomial_eval]) (by rwa [he])
  exact ⟨n,by simpa only [dividedPolynomial_eval] using hn⟩

/-- Traces of divided distance polynomials satisfy the homogeneous Chebyshev
recurrence, since all the nonconstant distance matrices have zero diagonal. -/
theorem trace_divided_distancePolynomial {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (s t r : ℝ) (h : ℕ)
    (htrace : ∀ k, 0<k → k≤h → (aeval A (distancePolynomial s t k)).trace=0)
    (k : ℕ) (hk : k≤h+1) :
    (aeval A (dividedPolynomial (distancePolynomial s t k) r)).trace =
      if k=0 then 0 else Fintype.card I * (spectralPolynomial s t (k-1)).eval r := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [distancePolynomial,←C_1,dividedPolynomial_C]
    simp
  | one => simp [distancePolynomial,spectralPolynomial]
  | more k ih₀ ih₁ =>
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    rw [distancePolynomial,dividedPolynomial_recurrence]
    simp only [aeval_add,aeval_sub,aeval_mul,aeval_C,Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc,one_mul,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,
      htrace (k+1) (by omega) (by omega),h₀,h₁,show k+1≠0 by omega,
      show k+2≠0 by omega,ite_false,zero_add,Nat.add_sub_cancel]
    cases k with
    | zero => simp [spectralPolynomial]; ring
    | succ k =>
      simp only [Nat.succ_ne_zero,ite_false,show k.succ-1=k by omega]
      rw [show k.succ+2-1=k+2 by omega,spectralPolynomial]
      simp only [eval_sub,eval_mul,eval_X,eval_C]
      ring
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityMultiplicityDecidableEq : DecidableEq V := Classical.decEq _

private theorem even_trace_distancePolynomial (D : Datum G (2*h) s t) (hh : 2≤h)
    (k : ℕ) (hk : 0<k) (hkh : k≤h) :
    (aeval (D.distanceMatrix 1) (distancePolynomial s t k)).trace=0 := by
  rw [D.even_distancePolynomial_aeval hh k hkh, Matrix.trace_smul,
    D.trace_distanceMatrix k hk,smul_zero]

private theorem odd_trace_distancePolynomial (D : Datum G (2*h+1) s t) (hh : 0<h)
    (k : ℕ) (hk : 0<k) (hkh : k≤h) :
    (aeval (D.distanceMatrix 1) (distancePolynomial s t k)).trace=0 := by
  rw [D.odd_distancePolynomial_aeval hh k hkh,D.trace_distanceMatrix k hk]

/-- The numerator in the even polygon's simple-eigenvalue multiplicity. -/
theorem even_trace_dividedAnnihilator (D : Datum G (2*h) s t) (hh : 2≤h) (r : ℝ) :
    (aeval (D.distanceMatrix 1) (dividedPolynomial (evenAnnihilator h s t) r)).trace =
      Fintype.card D.Point *
        ((r-((s:ℝ)-1)*(t+1))*(spectralPolynomial s t (h-1)).eval r -
          (s:ℝ)*t*(t+1)*(spectralPolynomial s t (h-2)).eval r) := by
  have ht := trace_divided_distancePolynomial (D.distanceMatrix 1) s t r h
    (D.even_trace_distancePolynomial hh)
  rw [evenAnnihilator,dividedPolynomial_recurrence]
  simp only [aeval_sub,aeval_add,aeval_mul,aeval_C,Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc,one_mul,Matrix.trace_sub,Matrix.trace_add,Matrix.trace_smul,
    D.even_trace_distancePolynomial hh h (by omega) le_rfl,
    ht h (by omega), ht (h-1) (by omega),show h≠0 by omega,
    show h-1≠0 by omega,ite_false,zero_add,smul_eq_mul,
    show h-1-1=h-2 by omega]
  ring

/-- The actual even point operator has integral simple-root multiplicities. -/
theorem even_multiplicity (D : Datum G (2*h) s t) (hh : 2≤h) (r : ℝ)
    (hr : (evenAnnihilator h s t).eval r=0)
    (hd : (evenAnnihilator h s t).derivative.eval r≠0) :
    ∃ n : ℕ, Fintype.card D.Point *
        ((r-((s:ℝ)-1)*(t+1))*(spectralPolynomial s t (h-1)).eval r -
          (s:ℝ)*t*(t+1)*(spectralPolynomial s t (h-2)).eval r) =
      (evenAnnihilator h s t).derivative.eval r*n := by
  obtain ⟨n,hn⟩ := exists_nat_matrix_trace_dividedPolynomial (D.distanceMatrix 1)
    (evenAnnihilator h s t) r hr hd (D.evenAnnihilator_aeval hh)
  exact ⟨n,by rwa [D.even_trace_dividedAnnihilator hh] at hn⟩
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial
private theorem oddAnnihilator_eq_distancePolynomial (h : ℕ) (s t : ℝ) (hh : 0<h) :
    oddAnnihilator h s t=distancePolynomial s t (h+1)-C (s*t)*distancePolynomial s t h := by
  obtain ⟨k,rfl⟩ : ∃ k,h=k+1 := ⟨h-1,by omega⟩
  simp only [oddAnnihilator,Nat.add_sub_cancel,
    show k+1=1 ↔ k=0 by omega, show k+1+1=k+2 by omega,distancePolynomial.eq_3]
  simp only [map_sub,map_add,map_mul]
  ring
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityMultiplicityDecidableEq2 : DecidableEq V := Classical.decEq _

/-- The numerator in the odd polygon's simple-eigenvalue multiplicity. -/
theorem odd_trace_dividedAnnihilator (D : Datum G (2*h+1) s t) (hh : 0<h) (r : ℝ) :
    (aeval (D.distanceMatrix 1) (dividedPolynomial (oddAnnihilator h s t) r)).trace =
      Fintype.card D.Point * ((spectralPolynomial s t h).eval r -
        (s:ℝ)*t*(spectralPolynomial s t (h-1)).eval r) := by
  have ht := trace_divided_distancePolynomial (D.distanceMatrix 1) s t r h
    (D.odd_trace_distancePolynomial hh)
  rw [oddAnnihilator_eq_distancePolynomial h s t hh]
  simp only [dividedPolynomial_sub,dividedPolynomial_C_mul,
    aeval_sub,aeval_mul,aeval_C,Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc,one_mul,Matrix.trace_sub,Matrix.trace_smul,
    ht (h+1) le_rfl,ht h (by omega),show h+1≠0 by omega,
    show h≠0 by omega,ite_false,Nat.add_sub_cancel,smul_eq_mul]
  ring

/-- The actual odd point operator has integral simple-root multiplicities. -/
theorem odd_multiplicity (D : Datum G (2*h+1) s t) (hh : 0<h) (r : ℝ)
    (hr : (oddAnnihilator h s t).eval r=0)
    (hd : (oddAnnihilator h s t).derivative.eval r≠0) :
    ∃ n : ℕ, Fintype.card D.Point * ((spectralPolynomial s t h).eval r -
        (s:ℝ)*t*(spectralPolynomial s t (h-1)).eval r) =
      (oddAnnihilator h s t).derivative.eval r*n := by
  obtain ⟨n,hn⟩ := exists_nat_matrix_trace_dividedPolynomial (D.distanceMatrix 1)
    (oddAnnihilator h s t) r hr hd (D.oddAnnihilator_aeval hh)
  exact ⟨n,by rwa [D.odd_trace_dividedAnnihilator hh] at hn⟩
end SimpleGraph.PolygonParameters.Datum
