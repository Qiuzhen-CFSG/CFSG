module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.Substitution
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.ExponentReduction
public import Mathlib.Tactic.LinearCombination

/-!
# Unique resonant monomial in the D4 root-weight region

Twice rho has simple-root coordinates (6,10,6,6) in the published root order.
We prove that a nonnegative exponent vector bounded by 2(q-1)rho can have
positive multiples of q^3-1 on its three folded cubic coordinates and of q-1
on its three singleton coordinates only when all twelve entries equal q-1.
The proof works for every integer q>1, in particular q=2.

This controls ALL terms that can become the reduced mixed-grid top. It does
not assert that the chart of a given global section satisfies the weight
bound; that representation-theoretic obligation remains with the extremal
assembly. Source: the root expansion in `PositiveRootCoordinates.Roots`;
Steinberg, `Chapter2St2.tex`, 13.2(d)--13.3(a), and [26], Sections 8--9.
-/

@[expose] public noncomputable section
open scoped BigOperators Classical
open Triality.Standard
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds

private theorem first_digit_bound {q a b c m : ℤ} (_hq : 1 < q)
    (ha : 0 ≤ a) (hm : 1 ≤ m)
    (h : a + q*b + q^2*c = (q^3-1)*m) : q ≤ a + m := by
  apply Int.le_of_dvd (by omega)
  refine ⟨q^2*m-b-q*c, ?_⟩
  nlinarith only [h]

set_option backward.isDefEq.respectTransparency false in
/-- Under the four D4 weight bounds, positive resonances in all six orbit
coordinates force every original root exponent to be q-1. The elementary
step is: a+qb+q^2c=(q^3-1)m, a≥0, m≥1 implies a+m≥q. Three uses of
this bound first force the last cubic and singleton multiplicities to one;
the remaining equations then force all twelve exponents. -/
theorem root_weight_resonant_unique {q : ℤ} (hq : 1 < q)
    (d : Fin 12 → ℤ) (m : Fin 6 → ℤ)
    (hd : ∀ i, 0 ≤ d i) (hm : ∀ i, 1 ≤ m i)
    (h0 : d 0+d 4+d 7+d 9+d 10+d 11 ≤ 6*(q-1))
    (h1 : d 3+d 4+d 5+d 6+d 7+d 8+d 9+d 10+2*d 11 ≤ 10*(q-1))
    (h2 : d 1+d 5+d 7+d 8+d 10+d 11 ≤ 6*(q-1))
    (h3 : d 2+d 6+d 8+d 9+d 10+d 11 ≤ 6*(q-1))
    (ha : d 0+q*d 1+q^2*d 2 = (q^3-1)*m 0)
    (hb : d 4+q*d 5+q^2*d 6 = (q^3-1)*m 1)
    (hc : d 7+q*d 8+q^2*d 9 = (q^3-1)*m 2)
    (hs0 : d 3=(q-1)*m 3)
    (hs1 : d 10=(q-1)*m 4)
    (hs2 : d 11=(q-1)*m 5) :
    ∀ i, d i = q-1 := by
  have hq3 : 0 < q^3-1 := by nlinarith
  have hi : m 0+m 1+(q+1)*m 2+m 4+m 5-6 ≤ d 9 := by
    have he : (q^3-1)*((m 0+m 1+(q+1)*m 2+m 4+m 5-6)-d 9) ≤ 0 := by
      linear_combination h0 + q*h2 + q^2*h3 - ha - hb - (q+1)*hc -
        (1+q+q^2)*hs1 - (1+q+q^2)*hs2
    nlinarith only [he, hq3]
  have had := first_digit_bound hq (hd 0) (hm 0) ha
  have hbd := first_digit_bound hq (hd 4) (hm 1) hb
  have hcd := first_digit_bound hq (hd 7) (hm 2) hc
  have hsum : m 2+m 4+m 5 ≤ 3 := by
    have h : q*(m 2+m 4+m 5-3) ≤ 0 := by
      nlinarith only [h0, hi, hs1, hs2, had, hbd, hcd]
    nlinarith
  have hm2 : m 2=1 := by have := hm 2; have := hm 4; have := hm 5; omega
  have hm4 : m 4=1 := by have := hm 2; have := hm 4; have := hm 5; omega
  have hm5 : m 5=1 := by have := hm 2; have := hm 4; have := hm 5; omega
  simp only [hm2, hm4, hm5] at hi hs1 hs2 hc hcd
  have hd0 : d 0=q-m 0 := by nlinarith only [h0, hi, hs1, hs2, had, hbd, hcd]
  have hd4 : d 4=q-m 1 := by nlinarith only [h0, hi, hs1, hs2, had, hbd, hcd]
  have hd7 : d 7=q-1 := by nlinarith only [h0, hi, hs1, hs2, had, hbd, hcd, hm2]
  have hc' : d 8+q*d 9=q^2-1 := by
    have : q*(d 8+q*d 9-(q^2-1))=0 := by nlinarith only [hc, hd7]
    have := (mul_eq_zero.mp this).resolve_left (by omega : q ≠ 0)
    omega
  have hd8ge : q ≤ d 8+1 := by
    apply Int.le_of_dvd (by have := hd 8; omega)
    exact ⟨q-d 9, by nlinarith only [hc']⟩
  have hd9le : d 9 ≤ q-1 := by nlinarith only [hc', hd8ge, hq]
  have hm0 : m 0=1 := by have := hm 0; have := hm 1; omega
  have hm1 : m 1=1 := by have := hm 0; have := hm 1; omega
  rw [hm0] at hd0 ha
  rw [hm1] at hd4 hb
  have hd9 : d 9=q-1 := by omega
  have hd8 : d 8=q-1 := by linear_combination hc' - q*hd9
  have ha' : d 1+q*d 2=q^2-1 := by
    have : q*(d 1+q*d 2-(q^2-1))=0 := by nlinarith only [ha, hd0]
    have := (mul_eq_zero.mp this).resolve_left (by omega : q ≠ 0)
    omega
  have hb' : d 5+q*d 6=q^2-1 := by
    have : q*(d 5+q*d 6-(q^2-1))=0 := by nlinarith only [hb, hd4]
    have := (mul_eq_zero.mp this).resolve_left (by omega : q ≠ 0)
    omega
  have hd1ge : q ≤ d 1+1 := by
    apply Int.le_of_dvd (by have := hd 1; omega)
    exact ⟨q-d 2, by nlinarith only [ha']⟩
  have hd5ge : q ≤ d 5+1 := by
    apply Int.le_of_dvd (by have := hd 5; omega)
    exact ⟨q-d 6, by nlinarith only [hb']⟩
  have hd1 : d 1=q-1 := by nlinarith only [h2, hd7, hd8, hs1, hs2, hd1ge, hd5ge]
  have hd5 : d 5=q-1 := by nlinarith only [h2, hd7, hd8, hs1, hs2, hd1ge, hd5ge]
  have hd2 : d 2=q-1 := by nlinarith only [ha', hd1, hq]
  have hd6 : d 6=q-1 := by nlinarith only [hb', hd5, hq]
  have hd3 : d 3=q-1 := by
    have hm3 := hm 3
    nlinarith only [h1, hd4, hd5, hd6, hd7, hd8, hd9, hs1, hs2, hs0, hm3, hq]
  have hd10 : d 10=q-1 := by nlinarith only [hs1]
  have hd11 : d 11=q-1 := by nlinarith only [hs2]
  intro i
  fin_cases i <;> first
  | exact hd0
  | exact hd1
  | exact hd2
  | exact hd3
  | exact hd4
  | exact hd5
  | exact hd6
  | exact hd7
  | exact hd8
  | exact hd9
  | exact hd10
  | exact hd11

/-- The four simple-root coordinates of the monomial are bounded by 2(q-1)rho. -/
def RootWeightBound (q : ℕ) (d : Fin 12 →₀ ℕ) : Prop :=
  d 0+d 4+d 7+d 9+d 10+d 11 ≤ 6*(q-1) ∧
  d 3+d 4+d 5+d 6+d 7+d 8+d 9+d 10+2*d 11 ≤ 10*(q-1) ∧
  d 1+d 5+d 7+d 8+d 10+d 11 ≤ 6*(q-1) ∧
  d 2+d 6+d 8+d 9+d 10+d 11 ≤ 6*(q-1)

set_option backward.isDefEq.respectTransparency false in
lemma reduced_fold_top_unique (P : Parameters) (d : Fin 12 →₀ ℕ)
    (hd : RootWeightBound P.q d)
    (he : reduceExponent (CoordinateField P) (foldExponent P.q d) =
      PolynomialSums.topExponent (CoordinateField P)) :
    d = rootTopExponent P.q := by
  choose r hr he using ((reduceExponent_eq_top_iff _ _).mp he)
  let m : Fin 6 → ℕ := ![r (.inl 0), r (.inl 1), r (.inl 2),
    r (.inr 0), r (.inr 1), r (.inr 2)]
  have hq : 1 < P.q := by have := P.q_ge_two; omega
  have hq1 : 1 ≤ P.q := by omega
  have hq3 : 1 ≤ P.q^3 := one_le_pow₀ hq1
  have ha := he (.inl 0)
  have hb := he (.inl 1)
  have hc := he (.inl 2)
  have hs0 := he (.inr 0)
  have hs1 := he (.inr 1)
  have hs2 := he (.inr 2)
  simp only [foldExponent_cubic, foldExponent_singleton, card_cubic, card_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at ha hb hc hs0 hs1 hs2
  have hm : ∀ i, (1:ℤ) ≤ m i := by
    have h0 := hr (.inl 0)
    have h1 := hr (.inl 1)
    have h2 := hr (.inl 2)
    have h3 := hr (.inr 0)
    have h4 := hr (.inr 1)
    have h5 := hr (.inr 2)
    intro i
    fin_cases i <;> dsimp [m] <;> omega
  have hbound := root_weight_resonant_unique (q := (P.q : ℤ)) (by exact_mod_cast hq)
    (fun i => (d i : ℤ)) (fun i => (m i : ℤ)) (fun i => Nat.cast_nonneg _) hm
    (by exact_mod_cast hd.1) (by exact_mod_cast hd.2.1)
    (by exact_mod_cast hd.2.2.1) (by exact_mod_cast hd.2.2.2)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) (by exact_mod_cast hs2)
  ext i
  have hi := hbound i
  change d i = P.q-1
  exact_mod_cast (show (d i : ℤ) = ((P.q-1 : ℕ) : ℤ) by
    simpa only [Nat.cast_sub hq1, Nat.cast_one] using hi)


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds
