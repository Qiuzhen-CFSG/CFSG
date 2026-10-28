module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.EvenSpectrum
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
public import Mathlib.NumberTheory.Niven

/-!
# The allowed even polygon gonalities

The paired multiplicity equations make each shifted angular root rational.
The first root makes `cos (2*pi/h)` rational. Niven's theorem restricts the
half-gonality to 2, 3, 4 or 6. At half-gonality 6 the roots at angles `pi/3`
and `pi/6` would make `cos (pi/6)` rational, a contradiction. The digon is
kept separately, giving even gonalities 2, 4, 6 and 8.

This proves the even branch of the Feit--Higman finite-polygon theorem,
J. Algebra 1 (1964), 114--131, cited by Fong--Seitz I (1J), printed p.6.
The rational-angle step uses Mathlib's proved Niven theorem. Thickness and
the point witness are explicit throughout.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial Real

theorem spectralPolynomial_cos_of_sq (s t w θ : ℝ) (hw : w^2=s*t) (k : ℕ) :
    (spectralPolynomial s t k).eval (s-1+2*w*cos θ)*sin θ =
      w^k*sin (((k:ℝ)+1)*θ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [spectralPolynomial]
  | one =>
    norm_num [spectralPolynomial]
    rw [Real.sin_two_mul]
    ring
  | more k ih₀ ih₁ =>
    have hv : (spectralPolynomial s t (k+2)).eval (s-1+2*w*cos θ) =
        2*w*cos θ*(spectralPolynomial s t (k+1)).eval (s-1+2*w*cos θ) -
        w*w*(spectralPolynomial s t k).eval (s-1+2*w*cos θ) := by
      rw [spectralPolynomial]
      simp only [eval_sub,eval_mul,eval_X,eval_C]
      rw [←hw]
      ring
    rw [hv,sub_mul,mul_assoc (2*w*cos θ),mul_assoc (w*w),ih₀,ih₁]
    have hsin : sin (((k:ℝ)+3)*θ)+sin (((k:ℝ)+1)*θ)=
        2*sin (((k:ℝ)+2)*θ)*cos θ := by
      rw [Real.sin_add_sin]
      congr 2 <;> ring
    push_cast
    rw [pow_succ,pow_succ,show (k:ℝ)+1+1=k+2 by ring,
      show (k:ℝ)+2+1=k+3 by ring]
    linear_combination -w^k*w^2*hsin
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality Real
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityEvenExclusionDecidableEq : DecidableEq V := Classical.decEq _

/-- Every angular root in the even spectrum is rational after its natural shift. -/
theorem even_angular_root_rational (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) (θ : ℝ)
    (hθ : 0<θ ∧ θ<π) (hperiod : sin ((h:ℝ)*θ)=0) :
    ∃ a : ℚ,2*sqrt ((s:ℝ)*t)*cos θ=(a:ℝ) := by
  let w : ℝ := sqrt ((s:ℝ)*t)
  have hw : w^2=(s:ℝ)*t := Real.sq_sqrt (by positivity)
  have hwpos : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hsin : sin θ≠0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hr : (spectralPolynomial s t (h-1)).eval ((s:ℝ)-1+2*w*cos θ)=0 := by
    apply mul_right_cancel₀ hsin
    rw [spectralPolynomial_cos_of_sq (s:ℝ) (t:ℝ) w θ hw,zero_mul]
    have he : ((h-1:ℕ):ℝ)+1=(h:ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one]
      ring
    rw [he,hperiod,mul_zero]
  have hy : (2*w*cos θ)^2<4*(s:ℝ)*t := by
    have hcos : cos θ^2<1 := by
      nlinarith [sin_sq_add_cos_sq θ,sq_pos_of_ne_zero hsin]
    have hprod := mul_pos (sq_pos_of_pos hwpos) (sub_pos.mpr hcos)
    nlinarith [hw]
  exact D.even_spectral_root_rational hh hs ht hp (2*w*cos θ) hy hr

/-- Rationality of the first paired root leaves half-gonalities 2, 3, 4, 6. -/
theorem even_half_alternatives (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) :
    h=2 ∨ h=3 ∨ h=4 ∨ h=6 := by
  let θ : ℝ := π/(h:ℝ)
  have hh0 : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have hh2 : (2:ℝ)≤h := by exact_mod_cast hh
  have hθ : 0<θ ∧ θ<π := by
    dsimp [θ]
    constructor
    · positivity
    · apply (div_lt_iff₀ hh0).mpr
      nlinarith [pi_pos]
  have hperiod : sin ((h:ℝ)*θ)=0 := by
    have he : (h:ℝ)*θ=π := by dsimp [θ]; field_simp
    rw [he,sin_pi]
  obtain ⟨a,ha⟩ := D.even_angular_root_rational hh hs ht hp θ hθ hperiod
  have hw : sqrt ((s:ℝ)*t)^2=(s:ℝ)*t := Real.sq_sqrt (by positivity)
  have hs0 : (s:ℝ)≠0 := by positivity
  have ht0 : (t:ℝ)≠0 := by positivity
  have ha2 : (a:ℝ)^2=4*(s:ℝ)*t*cos θ^2 := by
    rw [←ha]
    calc
      _ = 4*sqrt ((s:ℝ)*t)^2*cos θ^2 := by ring
      _ = _ := by rw [hw]; ring
  have hcos : ∃ b : ℚ,cos (2*θ)=(b:ℝ) := by
    refine ⟨a^2/(2*s*t)-1,?_⟩
    push_cast
    rw [cos_two_mul]
    field_simp
    nlinarith [ha2]
  have hθ' : 2*θ=((2/(h:ℚ):ℚ):ℝ)*π := by dsimp [θ]; push_cast; ring
  rw [hθ'] at hcos
  have hb : (2/(h:ℚ):ℚ) ∈ Set.Icc 0 1 := by
    have hh0' : (0:ℚ)<h := by exact_mod_cast (show 0<h by omega)
    constructor
    · positivity
    · apply (div_le_iff₀ hh0').mpr
      simpa only [one_mul] using (show (2:ℚ)≤h by exact_mod_cast hh)
  have hn := niven_angle_div_pi_eq hcos hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
  rcases hn with hz|hz|hz|hz|hz
  all_goals
    field_simp at hz
    norm_cast at hz <;> omega

/-- The two angular roots at half-gonality six would make `cos (pi/6)` rational. -/
theorem even_half_ne_six (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) : h≠6 := by
  intro he
  subst h
  have hbnd3 : 0<π/3 ∧ π/3<π := by constructor <;> linarith [pi_pos]
  have hbnd6 : 0<π/6 ∧ π/6<π := by constructor <;> linarith [pi_pos]
  have hp3 : sin ((6:ℝ)*(π/3))=0 := by
    rw [show (6:ℝ)*(π/3)=2*π by ring,sin_two_pi]
  have hp6 : sin ((6:ℝ)*(π/6))=0 := by
    rw [show (6:ℝ)*(π/6)=π by ring,sin_pi]
  obtain ⟨b,hb⟩ := D.even_angular_root_rational hh hs ht hp (π/3) hbnd3 hp3
  obtain ⟨a,ha⟩ := D.even_angular_root_rational hh hs ht hp (π/6) hbnd6 hp6
  rw [cos_pi_div_three] at hb
  have hb' : sqrt ((s:ℝ)*t)=(b:ℝ) := by linarith
  have hb0 : (b:ℝ)≠0 := by rw [←hb']; positivity
  have hcos : cos (π/6)=((a/(2*b):ℚ):ℝ) := by
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb0)).mpr
    rw [hb'] at ha
    linear_combination ha
  have hi : Irrational (cos (π/6)) := by
    have hi := irrational_cos_rat_mul_pi (r:=1/6) (by norm_num)
    have he : (((1/6:ℚ):ℝ)*π)=π/6 := by norm_num; ring
    rw [he] at hi
    exact hi
  exact hi ⟨_,hcos.symm⟩

/-- The even branch of the finite thick polygon theorem. -/
theorem gonality_even_alternatives {m : ℕ} (D : Datum G m s t) (hm : 2≤m)
    (hs : 1<s) (ht : 1<t) (hp : ∃ v,D.color v=0) (he : Even m) :
    m=2 ∨ m=4 ∨ m=6 ∨ m=8 := by
  obtain ⟨h,heq⟩ := he
  have hm' : m=2*h := by omega
  clear heq
  subst m
  by_cases hh : h=1
  · left; omega
  · have hh' : 2≤h := by omega
    have ha := D.even_half_alternatives hh' hs ht hp
    have hn := D.even_half_ne_six hh' hs ht hp
    omega
end SimpleGraph.PolygonParameters.Datum
