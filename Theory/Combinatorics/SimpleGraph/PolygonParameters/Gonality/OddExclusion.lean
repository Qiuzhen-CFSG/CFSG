module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.OddSpectrum
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.OddSpectrum
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
public import Mathlib.NumberTheory.Niven

/-!
# Exclusion of thick odd polygons other than triangles

The first nonconstant spectral root is
`s-1+2*s*cos (2*pi/(2*h+1))`. Its rationality, proved from integral
multiplicities, makes this cosine rational. Niven's theorem leaves only
`h=1` among the positive integers. Thus the odd branch of the finite thick
polygon theorem is complete, using exactly the metric datum and thickness.

Source: the finite-polygon theorem of Feit--Higman, J. Algebra 1 (1964),
114--131, cited by Fong--Seitz I (1J), printed p.6. The final elementary
rational-angle step uses Mathlib's proved Niven theorem.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial Real

theorem spectralPolynomial_cos (q θ : ℝ) (k : ℕ) :
    (spectralPolynomial q q k).eval (q-1+2*q*cos θ)*sin θ =
      q^k*sin (((k:ℝ)+1)*θ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one =>
    norm_num [spectralPolynomial]
    rw [Real.sin_two_mul]
    ring
  | more k ih₀ ih₁ =>
    have hv : (spectralPolynomial q q (k+2)).eval (q-1+2*q*cos θ) =
        2*q*cos θ*(spectralPolynomial q q (k+1)).eval (q-1+2*q*cos θ) -
        q*q*(spectralPolynomial q q k).eval (q-1+2*q*cos θ) := by
      rw [spectralPolynomial]
      simp only [eval_sub,eval_mul,eval_X,eval_C]
      ring
    rw [hv,sub_mul,mul_assoc (2*q*cos θ),mul_assoc (q*q),ih₀,ih₁]
    have hsin : sin (((k:ℝ)+3)*θ)+sin (((k:ℝ)+1)*θ)=
        2*sin (((k:ℝ)+2)*θ)*cos θ := by
      rw [Real.sin_add_sin]
      congr 2 <;> ring
    push_cast
    rw [pow_succ,pow_succ,show (k:ℝ)+1+1=k+2 by ring,
      show (k:ℝ)+2+1=k+3 by ring]
    linear_combination -q^k*q^2*hsin

/-- The first angular root of the odd spectrum, for every possible odd gonality. -/
theorem oddSpectralPolynomial_first_root (h : ℕ) (hh : 0<h) (q : ℝ) :
    (oddSpectralPolynomial h q).eval
      (q-1+2*q*cos (2*π/(2*(h:ℝ)+1)))=0 := by
  let θ : ℝ := 2*π/(2*(h:ℝ)+1)
  have hden : (0:ℝ)<2*h+1 := by positivity
  have hh' : (1:ℝ)≤h := by exact_mod_cast hh
  have hθ : 0<θ ∧ θ<π := by
    dsimp [θ]
    constructor
    · positivity
    · apply (div_lt_iff₀ hden).mpr
      nlinarith [pi_pos]
  have hsin : sin θ≠0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hsum : sin (((h:ℝ)+1)*θ)+sin ((h:ℝ)*θ)=0 := by
    rw [Real.sin_add_sin]
    have he : (((h:ℝ)+1)*θ+(h:ℝ)*θ)/2=π := by
      dsimp [θ]
      field_simp
      ring
    rw [he,sin_pi,mul_zero,zero_mul]
  apply mul_right_cancel₀ hsin
  rw [zero_mul]
  change (oddSpectralPolynomial h q).eval (q-1+2*q*cos θ)*sin θ=0
  simp only [oddSpectralPolynomial,eval_add,eval_mul,eval_C]
  rw [add_mul,mul_assoc q,spectralPolynomial_cos,spectralPolynomial_cos]
  have he : ((h-1:ℕ):ℝ)+1=(h:ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    ring
  rw [he]
  have hp : q*q^(h-1)=q^h := by rw [←pow_succ',Nat.sub_add_cancel (by omega)]
  rw [←mul_assoc,hp,←mul_add,hsum,mul_zero]
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality Real
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityOddExclusionDecidableEq : DecidableEq V := Classical.decEq _

/-- A finite thick polygon of odd gonality has gonality three. -/
theorem odd_half_eq_one (D : Datum G (2*h+1) s t) (hh : 0<h)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) : h=1 := by
  have hpar : s=t := D.parameters_eq_of_odd (by omega) (by omega) (by omega) hp ⟨h,by omega⟩
  subst t
  let θ : ℝ := 2*π/(2*(h:ℝ)+1)
  obtain ⟨a,ha⟩ := D.odd_spectral_root_rational hh hs hp
    ((s:ℝ)-1+2*s*cos θ) (oddSpectralPolynomial_first_root h hh s)
  have hs0 : (s:ℝ)≠0 := by positivity
  have hcos : ∃ b : ℚ, cos θ=(b:ℝ) := by
    refine ⟨(a-(s:ℚ)+1)/(2*s),?_⟩
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) hs0)).mpr
    linear_combination ha
  have hθ : θ=((2/(2*(h:ℚ)+1):ℚ):ℝ)*π := by
    dsimp [θ]
    push_cast
    ring
  have hden : (0:ℚ)<2*h+1 := by positivity
  have hbounds : (2/(2*(h:ℚ)+1):ℚ) ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hden).mpr
      have : (1:ℚ)≤h := by exact_mod_cast hh
      linarith
  rw [hθ] at hcos
  have hn := niven_angle_div_pi_eq hcos hbounds
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
  rcases hn with hz|hz|hz|hz|hz
  all_goals
    field_simp at hz
    norm_cast at hz <;> omega

/-- The odd case of the allowed-gonality theorem, with the datum's original index. -/
theorem gonality_eq_three_of_odd {m : ℕ} (D : Datum G m s t) (hm : 2≤m)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) (ho : Odd m) : m=3 := by
  obtain ⟨h,he⟩ := ho
  have hm' : m=2*h+1 := by omega
  subst m
  have hh := D.odd_half_eq_one (by omega) hs ht hp
  omega
end SimpleGraph.PolygonParameters.Datum
