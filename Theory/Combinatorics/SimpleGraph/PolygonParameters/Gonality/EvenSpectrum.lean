module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.OddSpectrum
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
public import Mathlib.NumberTheory.Niven

/-!
# Rationality of the paired even spectrum

The derivative and Cassini identities simplify each nontrivial even
multiplicity. Apply the resulting equation to the two shifted roots `y`
and `-y`. Adding the normalized equations first makes `y^2` rational;
subtracting them then makes `y` rational. Thickness supplies both nonzero
determinants. The point witness supplies the positive matrix size.

This is the even multiplicity step in the Feit--Higman finite-polygon theorem
cited by Fong--Seitz I (1J), printed p.6. The proof uses the actual point
operator and its trace equations; no restriction on the gonality is assumed.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

theorem spectralPolynomial_root_derivative (s t r : ℝ) (h : ℕ) (hh : 2≤h)
    (hr : (spectralPolynomial s t (h-1)).eval r=0) :
    (4*s*t-(r-(s-1))^2)*(spectralPolynomial s t (h-1)).derivative.eval r =
      2*(h:ℝ)*s*t*(spectralPolynomial s t (h-2)).eval r := by
  have hd := spectralPolynomial_derivative s t r (h-1)
  rw [show h-1+1=h by omega,hr,mul_zero,zero_sub] at hd
  have hc := spectralPolynomial.eq_3 s t (h-2)
  rw [show (h-2).succ.succ=h by omega,show h-2+1=h-1 by omega] at hc
  rw [hc] at hd
  simp only [eval_sub,eval_mul,eval_X,eval_C,hr,mul_zero,zero_sub] at hd
  rw [Nat.cast_sub (by omega),Nat.cast_one] at hd
  linear_combination hd

theorem spectralPolynomial_root_prev_ne_zero (s t r : ℝ) (h : ℕ) (hh : 2≤h)
    (hb : s*t≠0) (hr : (spectralPolynomial s t (h-1)).eval r=0) :
    (spectralPolynomial s t (h-2)).eval r≠0 := by
  intro hz
  have hc := spectralPolynomial_cassini s t r (h-2)
  rw [show h-2+1=h-1 by omega,hr,hz] at hc
  simp only [zero_pow (by decide : 2≠0),zero_mul,sub_zero] at hc
  exact (pow_ne_zero _ hb) hc.symm

theorem spectralPolynomial_root_derivative_ne_zero (s t r : ℝ) (h : ℕ) (hh : 2≤h)
    (hb : s*t≠0) (hr : (spectralPolynomial s t (h-1)).eval r=0) :
    (spectralPolynomial s t (h-1)).derivative.eval r≠0 := by
  have he := spectralPolynomial_root_derivative s t r h hh hr
  intro hz
  rw [hz,mul_zero] at he
  have hn : (2:ℝ)*h≠0 := by positivity
  have he' : (2*(h:ℝ))*(s*t)*(spectralPolynomial s t (h-2)).eval r=0 := by
    linear_combination -he
  exact (mul_ne_zero (mul_ne_zero hn hb)
    (spectralPolynomial_root_prev_ne_zero s t r h hh hb hr)) he'

theorem spectralPolynomial_reflection (s t y : ℝ) (k : ℕ) :
    (spectralPolynomial s t k).eval (s-1-y) =
      (-1:ℝ)^k*(spectralPolynomial s t k).eval (s-1+y) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one => simp [spectralPolynomial]
  | more k ih₀ ih₁ =>
    rw [spectralPolynomial]
    simp only [eval_sub,eval_mul,eval_X,eval_C,ih₀,ih₁]
    rw [pow_succ,pow_succ]
    ring
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityEvenSpectrumDecidableEq : DecidableEq V := Classical.decEq _

/-- An interior even spectral root satisfies the integral multiplicity equation. -/
theorem even_multiplicity_equation (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 0<s) (ht : 0<t) (y : ℝ)
    (hr : (spectralPolynomial s t (h-1)).eval ((s:ℝ)-1+y)=0)
    (hval : y≠(s:ℝ)*t+1) (hleft : y≠-((s:ℝ)+t)) :
    ∃ n : ℕ, 2*(h:ℝ)*n*((y-(s:ℝ)*t-1)*(y+s+t)) =
      (Fintype.card D.Point:ℝ)*(t+1)*(y^2-4*s*t) := by
  let r : ℝ := (s:ℝ)-1+y
  have hb : (s:ℝ)*t≠0 := by positivity
  have hf := evenAnnihilator_factorization (s:ℝ) (t:ℝ) h hh
  have hr0 : (evenAnnihilator h s t).eval r=0 := by simp [hf,hr,r]
  have hd : (evenAnnihilator h s t).derivative.eval r =
      ((y-(s:ℝ)*t-1)*(y+s+t))*(spectralPolynomial s t (h-1)).derivative.eval r := by
    rw [hf]
    simp only [derivative_mul,derivative_sub,derivative_add,derivative_X,derivative_C,
      sub_zero,add_zero,one_mul,eval_add,eval_sub,eval_mul,eval_X,eval_C]
    change _+_*(spectralPolynomial s t (h-1)).derivative.eval r=_
    rw [show (spectralPolynomial s t (h-1)).eval r=0 from hr,mul_zero,zero_add]
    dsimp [r]
    ring
  have hd0 : (evenAnnihilator h s t).derivative.eval r≠0 := by
    rw [hd]
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro he; apply hval; linarith
      · intro he; apply hleft; linarith
    · exact spectralPolynomial_root_derivative_ne_zero s t r h hh hb hr
  obtain ⟨n,hn⟩ := D.even_multiplicity hh r hr0 hd0
  refine ⟨n,?_⟩
  have hu := spectralPolynomial_root_prev_ne_zero s t r h hh hb hr
  have hder := spectralPolynomial_root_derivative s t r h hh hr
  rw [hd] at hn
  rw [show (spectralPolynomial s t (h-1)).eval r=0 from hr,mul_zero,zero_sub] at hn
  have hy : r-((s:ℝ)-1)=y := by dsimp [r]; ring
  rw [hy] at hder
  apply mul_right_cancel₀ (mul_ne_zero hb hu)
  linear_combination (y^2-4*(s:ℝ)*t)*hn -
    n*((y-(s:ℝ)*t-1)*(y+s+t))*hder
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality

private theorem rational_of_paired_multiplicities (s t h N np nm : ℕ)
    (hs : 1<s) (ht : 1<t) (hh : 0<h) (hN : 0<N) (y : ℝ)
    (hy : y^2<4*(s:ℝ)*t)
    (hp : 2*(h:ℝ)*np*((y-(s:ℝ)*t-1)*(y+s+t)) =
      (N:ℝ)*(t+1)*(y^2-4*s*t))
    (hm : 2*(h:ℝ)*nm*((-y-(s:ℝ)*t-1)*(-y+s+t)) =
      (N:ℝ)*(t+1)*(y^2-4*s*t)) : ∃ a : ℚ,y=(a:ℝ) := by
  have hs' : (1:ℝ)<s := by exact_mod_cast hs
  have ht' : (1:ℝ)<t := by exact_mod_cast ht
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hnump : (N:ℝ)*(t+1)≠0 := by positivity
  have hnz : y^2-4*(s:ℝ)*t≠0 := ne_of_lt (sub_neg.mpr hy)
  have hnp : np≠0 := by
    intro hz
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul] at hp
    exact (mul_ne_zero hnump hnz) hp.symm
  have hnm : nm≠0 := by
    intro hz
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul] at hm
    exact (mul_ne_zero hnump hnz) hm.symm
  have hdp : (2*(h:ℝ)*np)≠0 := by positivity
  have hdm : (2*(h:ℝ)*nm)≠0 := by positivity
  let ap : ℚ := (N:ℚ)*(t+1)/(2*h*np)
  let am : ℚ := (N:ℚ)*(t+1)/(2*h*nm)
  have hp' : y^2+((s:ℝ)+t-s*t-1)*y-((s:ℝ)*t+1)*(s+t) =
      (ap:ℝ)*(y^2-4*s*t) := by
    dsimp [ap]
    push_cast
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hdp).mpr
    linear_combination hp
  have hm' : y^2-((s:ℝ)+t-s*t-1)*y-((s:ℝ)*t+1)*(s+t) =
      (am:ℝ)*(y^2-4*s*t) := by
    dsimp [am]
    push_cast
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hdm).mpr
    linear_combination hm
  have hc : (s:ℝ)+t-s*t-1≠0 := by
    have hpos : 0<((s:ℝ)-1)*(t-1) := mul_pos (by linarith) (by linarith)
    intro he
    nlinarith
  have hD : 4*(s:ℝ)*t<((s:ℝ)*t+1)*(s+t) := by
    have hs2 : (2:ℝ)≤s := by exact_mod_cast hs
    have ht2 : (2:ℝ)≤t := by exact_mod_cast ht
    have hpos : 0≤(s:ℝ)*t*(s+t-4) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hden : (2:ℝ)-ap-am≠0 := by
    intro hz
    have he : 2*(((s:ℝ)*t+1)*(s+t)-4*s*t)=0 := by
      linear_combination -hp' -hm' +(y^2-4*(s:ℝ)*t)*hz
    linarith
  let z : ℚ := (2*((s:ℚ)*t+1)*(s+t)-4*s*t*(ap+am))/(2-ap-am)
  have hz : y^2=(z:ℝ) := by
    dsimp [z]
    push_cast
    apply (eq_div_iff hden).mpr
    linear_combination hp'+hm'
  refine ⟨(ap-am)*(z-4*s*t)/(2*((s:ℚ)+t-s*t-1)),?_⟩
  push_cast
  apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).mpr
  rw [←hz]
  linear_combination hp'-hm'
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityEvenSpectrumDecidableEq2 : DecidableEq V := Classical.decEq _

/-- Paired roots and their integral multiplicities force the shifted even
spectral root to be rational. -/
theorem even_spectral_root_rational (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) (y : ℝ)
    (hy : y^2<4*(s:ℝ)*t)
    (hr : (spectralPolynomial s t (h-1)).eval ((s:ℝ)-1+y)=0) :
    ∃ a : ℚ,y=(a:ℝ) := by
  have hval (z : ℝ) (hz : z^2<4*(s:ℝ)*t) : z≠(s:ℝ)*t+1 := by
    intro he
    rw [he] at hz
    nlinarith [sq_nonneg ((s:ℝ)*t-1)]
  have hleft (z : ℝ) (hz : z^2<4*(s:ℝ)*t) : z≠-((s:ℝ)+t) := by
    intro he
    rw [he] at hz
    nlinarith [sq_nonneg ((s:ℝ)-t)]
  have hr' : (spectralPolynomial s t (h-1)).eval ((s:ℝ)-1+(-y))=0 := by
    rw [←sub_eq_add_neg,spectralPolynomial_reflection,hr,mul_zero]
  have hy' : (-y)^2<4*(s:ℝ)*t := by simpa only [neg_sq] using hy
  obtain ⟨np,hnp⟩ := D.even_multiplicity_equation hh (by omega) (by omega) y hr
    (hval y hy) (hleft y hy)
  obtain ⟨nm,hnm⟩ := D.even_multiplicity_equation hh (by omega) (by omega) (-y) hr'
    (hval (-y) hy') (hleft (-y) hy')
  simp only [neg_sq] at hnm
  have hN : 0<Fintype.card D.Point := by
    have : Nonempty D.Point := by obtain ⟨v,hv⟩ := hp; exact ⟨⟨v,hv⟩⟩
    exact Fintype.card_pos
  exact rational_of_paired_multiplicities s t h (Fintype.card D.Point) np nm
    hs ht (by omega) hN y hy hnp hnm
end SimpleGraph.PolygonParameters.Datum
