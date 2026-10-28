module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Multiplicity
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rationality of the odd polygon spectrum

The Chebyshev derivative and Cassini identities show that the nontrivial odd
spectral roots are simple. The projection-trace multiplicity formula then
reduces to a fractional linear equation in the eigenvalue. Its determinant
is nonzero precisely in the thick case, forcing each such root to be rational.

This develops the odd-order exclusion in the Feit--Higman finite-polygon
argument cited by Fong--Seitz I (1J), printed p.6. All identities and the
application to the literal point operator are proved here; no classification
assumption enters the spectrum.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

theorem spectralPolynomial_derivative (s t r : ℝ) (k : ℕ) :
    (4*s*t-(r-(s-1))^2)*(spectralPolynomial s t k).derivative.eval r =
      ((k:ℝ)+2)*(r-(s-1))*(spectralPolynomial s t k).eval r -
        2*((k:ℝ)+1)*(spectralPolynomial s t (k+1)).eval r := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one => simp [spectralPolynomial]; ring
  | more k ih₀ ih₁ =>
    have hd : (spectralPolynomial s t (k+2)).derivative.eval r =
        (spectralPolynomial s t (k+1)).eval r +
        (r-(s-1))*(spectralPolynomial s t (k+1)).derivative.eval r -
        s*t*(spectralPolynomial s t k).derivative.eval r := by
      rw [spectralPolynomial]
      simp only [derivative_sub,derivative_mul,derivative_X,derivative_C,sub_zero,
        zero_mul,sub_zero,one_mul,zero_add,eval_sub,eval_add,eval_mul,eval_X,eval_C]
    rw [hd]
    calc
      _ = (4*s*t-(r-(s-1))^2)*(spectralPolynomial s t (k+1)).eval r +
          (r-(s-1))*((4*s*t-(r-(s-1))^2)*
            (spectralPolynomial s t (k+1)).derivative.eval r) -
          s*t*((4*s*t-(r-(s-1))^2)*(spectralPolynomial s t k).derivative.eval r) := by ring
      _ = _ := by
        rw [ih₀,ih₁,show k+2+1=(k+1)+2 by omega,spectralPolynomial.eq_3 s t (k+1)]
        rw [spectralPolynomial.eq_3 s t k]
        simp only [eval_sub,eval_mul,eval_X,eval_C,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring

theorem spectralPolynomial_cassini (s t r : ℝ) (k : ℕ) :
    (spectralPolynomial s t (k+1)).eval r ^ 2 -
      (spectralPolynomial s t k).eval r*(spectralPolynomial s t (k+2)).eval r =
        (s*t)^(k+1) := by
  induction k with
  | zero => simp [spectralPolynomial]; ring
  | succ k ih =>
    change (spectralPolynomial s t (k+2)).eval r ^ 2 -
      (spectralPolynomial s t (k+1)).eval r*(spectralPolynomial s t (k+1+2)).eval r = _
    calc
      _ = s*t*((spectralPolynomial s t (k+1)).eval r ^ 2 -
          (spectralPolynomial s t k).eval r*(spectralPolynomial s t (k+2)).eval r) := by
        rw [spectralPolynomial.eq_3 s t (k+1),spectralPolynomial.eq_3 s t k]
        simp only [eval_sub,eval_mul,eval_X,eval_C]
        ring
      _ = _ := by rw [ih,pow_succ]; ring

theorem spectralPolynomial_eval_left (q : ℝ) (k : ℕ) :
    (spectralPolynomial q q k).eval (-q-1)=(-q)^k*((k:ℝ)+1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one => simp [spectralPolynomial]; ring
  | more k ih₀ ih₁ =>
    rw [spectralPolynomial]
    simp only [eval_sub,eval_mul,eval_X,eval_C,ih₀,ih₁,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    rw [pow_succ,pow_succ]
    ring

/-- The polynomial factor associated with the nonconstant odd spectrum. -/
def oddSpectralPolynomial (h : ℕ) (q : ℝ) : ℝ[X] :=
  spectralPolynomial q q h+C q*spectralPolynomial q q (h-1)

theorem oddSpectralPolynomial_prev_ne_zero (h : ℕ) (hh : 0<h) (q r : ℝ) (hq : q≠0)
    (hr : (oddSpectralPolynomial h q).eval r=0) :
    (spectralPolynomial q q (h-1)).eval r≠0 := by
  intro hz
  have hz' : (spectralPolynomial q q h).eval r=0 := by
    simpa [oddSpectralPolynomial,hz] using hr
  by_cases he : h=1
  · simp [he,spectralPolynomial] at hz
  · have hc := spectralPolynomial_cassini q q r (h-2)
    rw [show h-2+1=h-1 by omega,show h-2+2=h by omega,hz,hz'] at hc
    simp only [zero_pow (by decide : 2≠0),mul_zero,sub_zero] at hc
    exact (pow_ne_zero _ (mul_ne_zero hq hq)) hc.symm

theorem oddSpectralPolynomial_left_ne_zero (h : ℕ) (hh : 0<h) (q : ℝ) (hq : q≠0) :
    (oddSpectralPolynomial h q).eval (-q-1)≠0 := by
  have he : h-1+1=h := by omega
  have hv : (oddSpectralPolynomial h q).eval (-q-1)=(-q)^h := by
    simp only [oddSpectralPolynomial,eval_add,eval_mul,eval_C,spectralPolynomial_eval_left]
    have hp : (-q)^h=(-q)^(h-1)*(-q) := by rw [←pow_succ,he]
    have hcast : ((h-1:ℕ):ℝ)=(h:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    rw [hp,hcast]
    ring
  rw [hv]
  exact pow_ne_zero _ (neg_ne_zero.mpr hq)

/-- The derivative at an odd spectral root has a simple closed form. -/
theorem oddSpectralPolynomial_derivative (h : ℕ) (hh : 0<h) (q r : ℝ) (hq : q≠0)
    (hr : (oddSpectralPolynomial h q).eval r=0) :
    (3*q-1-r)*(oddSpectralPolynomial h q).derivative.eval r =
      (2*(h:ℝ)+1)*q*(spectralPolynomial q q (h-1)).eval r := by
  have hleft : r+q+1≠0 := by
    intro he
    have he' : r=-q-1 := by linarith
    exact oddSpectralPolynomial_left_ne_zero h hh q hq (he' ▸ hr)
  have ha : (spectralPolynomial q q h).eval r = -q*(spectralPolynomial q q (h-1)).eval r := by
    have he := hr
    simp only [oddSpectralPolynomial,eval_add,eval_mul,eval_C] at he
    linear_combination he
  have h₀ := spectralPolynomial_derivative q q r (h-1)
  have h₁ := spectralPolynomial_derivative q q r h
  have he : h-1+1=h := by omega
  have hcast : ((h-1:ℕ):ℝ)=(h:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [he,hcast] at h₀
  have hrec : (spectralPolynomial q q (h+1)).eval r =
      (r-(q-1))*(spectralPolynomial q q h).eval r -q*q*(spectralPolynomial q q (h-1)).eval r := by
    have hr' := spectralPolynomial.eq_3 q q (h-1)
    have he' : (h-1).succ.succ=h+1 := by omega
    rw [he',he] at hr'
    rw [hr']
    simp only [eval_sub,eval_mul,eval_X,eval_C]
  have hd : (oddSpectralPolynomial h q).derivative.eval r =
      (spectralPolynomial q q h).derivative.eval r+q*(spectralPolynomial q q (h-1)).derivative.eval r := by
    simp only [oddSpectralPolynomial,derivative_add,derivative_mul,derivative_C,
      zero_mul,zero_add,eval_add,eval_mul,eval_C]
  apply mul_left_cancel₀ hleft
  rw [hd]
  rw [hrec,ha] at h₁
  rw [ha] at h₀
  linear_combination h₁+q*h₀

theorem oddSpectralPolynomial_derivative_ne_zero (h : ℕ) (hh : 0<h) (q r : ℝ) (hq : q≠0)
    (hr : (oddSpectralPolynomial h q).eval r=0) :
    (oddSpectralPolynomial h q).derivative.eval r≠0 := by
  have he := oddSpectralPolynomial_derivative h hh q r hq hr
  intro hz
  rw [hz,mul_zero] at he
  have hn : 2*(h:ℝ)+1≠0 := by positivity
  exact (mul_ne_zero (mul_ne_zero hn hq)
    (oddSpectralPolynomial_prev_ne_zero h hh q r hq hr)) he.symm
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

private theorem spectralPolynomial_valence_bounds (q : ℝ) (k : ℕ) :
    1≤(spectralPolynomial q q k).eval (q*(q+1)) ∧
      (spectralPolynomial q q k).eval (q*(q+1))≤
        (spectralPolynomial q q (k+1)).eval (q*(q+1)) := by
  induction k with
  | zero => simp [spectralPolynomial]; nlinarith [sq_nonneg q]
  | succ k ih =>
    constructor
    · exact le_trans ih.1 ih.2
    · rw [show k.succ+1=k+2 by omega,spectralPolynomial.eq_3 q q k]
      simp only [eval_sub,eval_mul,eval_X,eval_C]
      nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr ih.2)]

theorem oddSpectralPolynomial_valence_pos (h : ℕ) (q : ℝ) (hq : 0<q) :
    0<(oddSpectralPolynomial h q).eval (q*(q+1)) := by
  have h₀ := (spectralPolynomial_valence_bounds q h).1
  have h₁ := (spectralPolynomial_valence_bounds q (h-1)).1
  simp only [oddSpectralPolynomial,eval_add,eval_mul,eval_C]
  positivity
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h q : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityOddRationalDecidableEq : DecidableEq V := Classical.decEq _

/-- The odd multiplicity formula simplifies to a fractional linear equation. -/
theorem odd_multiplicity_equation (D : Datum G (2*h+1) q q) (hh : 0<h)
    (hq : 0<q) (r : ℝ) (hr : (oddSpectralPolynomial h q).eval r=0) :
    ∃ n : ℕ, (Fintype.card D.Point:ℝ)*(q+1)*(3*q-1-r) =
      (2*(h:ℝ)+1)*n*((q:ℝ)*(q+1)-r) := by
  have hq' : (q:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  have hf : oddAnnihilator h q q=(X-C ((q:ℝ)*(q+1)))*oddSpectralPolynomial h q :=
    oddAnnihilator_factorization q h hh
  have hval : r≠(q:ℝ)*(q+1) := by
    intro he
    rw [he] at hr
    exact (ne_of_gt (oddSpectralPolynomial_valence_pos h q (by exact_mod_cast hq))) hr
  have hd : (oddAnnihilator h q q).derivative.eval r =
      (r-(q:ℝ)*(q+1))*(oddSpectralPolynomial h q).derivative.eval r := by
    rw [hf]
    simp only [derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,
      one_mul,eval_add,hr,eval_mul,eval_sub,eval_X,eval_C,zero_add]
  have hd0 : (oddAnnihilator h q q).derivative.eval r≠0 := by
    rw [hd]
    exact mul_ne_zero (sub_ne_zero.mpr hval)
      (oddSpectralPolynomial_derivative_ne_zero h hh q r hq' hr)
  have hr0 : (oddAnnihilator h q q).eval r=0 := by simp [hf,hr]
  obtain ⟨n,hn⟩ := D.odd_multiplicity hh r hr0 hd0
  refine ⟨n,?_⟩
  have hu := oddSpectralPolynomial_prev_ne_zero h hh q r hq' hr
  have hder := oddSpectralPolynomial_derivative h hh q r hq' hr
  have hroot := hr
  simp only [oddSpectralPolynomial,eval_add,eval_mul,eval_C] at hroot
  rw [hd] at hn
  apply mul_right_cancel₀ (mul_ne_zero hq' hu)
  linear_combination -(3*(q:ℝ)-1-r)*hn -
    (r-(q:ℝ)*(q+1))*n*hder +
    (Fintype.card D.Point:ℝ)*(3*(q:ℝ)-1-r)*hroot

/-- Thickness makes the fractional linear multiplicity relation invertible;
therefore every nonconstant odd spectral root is rational. -/
theorem odd_spectral_root_rational (D : Datum G (2*h+1) q q) (hh : 0<h)
    (hq : 1<q) (hp : ∃ v,D.color v=0) (r : ℝ)
    (hr : (oddSpectralPolynomial h q).eval r=0) : ∃ a : ℚ,r=(a:ℝ) := by
  obtain ⟨n,hn⟩ := D.odd_multiplicity_equation hh (by omega) r hr
  have hq' : (1:ℝ)<q := by exact_mod_cast hq
  have hN : (0:ℝ)<Fintype.card D.Point := by
    have : Nonempty D.Point := by obtain ⟨v,hv⟩ := hp; exact ⟨⟨v,hv⟩⟩
    exact_mod_cast Fintype.card_pos
  have hden : (2*(h:ℝ)+1)*n-(Fintype.card D.Point:ℝ)*(q+1)≠0 := by
    intro hz
    have hz' := sub_eq_zero.mp hz
    rw [mul_assoc (2*(h:ℝ)+1),←mul_assoc (2*(h:ℝ)+1),hz'] at hn
    have hcoef : (Fintype.card D.Point:ℝ)*(q+1)≠0 := by positivity
    have he := (mul_left_cancel₀ hcoef) hn
    nlinarith [sq_pos_of_pos (sub_pos.mpr hq')]
  refine ⟨(((2*(h:ℚ)+1)*n*q*(q+1)-(Fintype.card D.Point:ℚ)*(q+1)*(3*q-1)) /
    ((2*(h:ℚ)+1)*n-(Fintype.card D.Point:ℚ)*(q+1))),?_⟩
  push_cast
  apply (eq_div_iff hden).mpr
  linear_combination hn
end SimpleGraph.PolygonParameters.Datum
