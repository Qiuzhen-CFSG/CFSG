module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AdditivePolynomialComposition
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Degrees of nonzero additive polynomials

This module proves the characteristic-power degree classification for additive
polynomials over an algebraically closed field.  In characteristic zero the
existing scaling argument gives degree one.  In positive characteristic,
additivity makes the derivative constant; subtracting the linear term leaves a
derivative-zero polynomial, which contracts through Frobenius.  Algebraic
closedness supplies the Frobenius roots needed to descend additivity, while
`Polynomial.expand_contract` gives strict degree descent.  Induction then
recovers the original degree as a power of the characteristic.

The result is the polynomial input for the additive parameter factors used in
the Steinberg endomorphism arguments.
-/

open scoped Polynomial
namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma additive_eval_zero_degree {f : Polynomial k}
    (hf : IsAdditivePolynomial f) : f.eval 0 = 0 := by
  have h := (isAdditivePolynomial_iff f).mp hf 0 0
  have h' := congrArg (fun z : k => z - f.eval 0) h
  simpa using h'.symm

private lemma additive_derivative_constant_degree (f : Polynomial k)
    (hf : IsAdditivePolynomial f) :
    ∃ c : k, f.derivative = Polynomial.C c := by
  have hf' := (isAdditivePolynomial_iff f).mp hf
  have htranslate (t : k) :
      f.comp (Polynomial.X + Polynomial.C t) = Polynomial.C (f.eval t) + f := by
    apply Polynomial.funext
    intro s
    simpa [Polynomial.eval_comp, add_comm] using hf' t s
  have hderivative_translate (t : k) :
      f.derivative.comp (Polynomial.X + Polynomial.C t) = f.derivative := by
    have h := congrArg Polynomial.derivative (htranslate t)
    simpa [Polynomial.derivative_comp] using h
  refine ⟨f.derivative.eval 0, ?_⟩
  apply Polynomial.funext
  intro t
  have h := congrArg (Polynomial.eval 0) (hderivative_translate t)
  simpa [Polynomial.eval_comp] using h

omit [IsAlgClosed k] in
private lemma additive_sub_linear_degree {f : Polynomial k} (hf : IsAdditivePolynomial f)
    (c : k) : IsAdditivePolynomial (f - Polynomial.C c * Polynomial.X) := by
  apply (isAdditivePolynomial_iff _).mpr
  intro s t
  have h := (isAdditivePolynomial_iff f).mp hf s t
  calc
    (f - Polynomial.C c * Polynomial.X).eval (s + t) =
        f.eval (s + t) - c * (s + t) := by simp [Polynomial.eval_sub, Polynomial.eval_mul]
    _ = (f.eval s - c * s) + (f.eval t - c * t) := by rw [h]; ring
    _ = (f - Polynomial.C c * Polynomial.X).eval s +
        (f - Polynomial.C c * Polynomial.X).eval t := by
          simp [Polynomial.eval_sub, Polynomial.eval_mul]

omit [IsAlgClosed k] in
private lemma additive_natDegree_pos_degree {f : Polynomial k}
    (hf : IsAdditivePolynomial f) (hne : f ≠ 0) : 0 < f.natDegree := by
  by_contra hpos
  have hzero : f.natDegree = 0 := Nat.eq_zero_of_not_pos hpos
  have hf0 : f.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact additive_eval_zero_degree hf
  apply hne
  rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, hf0]
  simp

private lemma contract_additive_of_derivative_zero_degree
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hf : IsAdditivePolynomial f)
    (hfder : f.derivative = 0) :
    IsAdditivePolynomial (Polynomial.contract p f) := by
  apply (isAdditivePolynomial_iff _).mpr
  intro s t
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq s (Fact.out : p.Prime).pos
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq t (Fact.out : p.Prime).pos
  have hxy : (x + y) ^ p = s + t := by
    simpa only [pow_one, hx, hy] using (add_pow_char_pow x y p 1)
  let g : Polynomial k := Polynomial.contract p f
  have hfg : Polynomial.expand k p g = f := by
    dsimp [g]
    exact Polynomial.expand_contract p hfder (Fact.out : p.Prime).ne_zero
  have h := (isAdditivePolynomial_iff f).mp hf x y
  have h' : g.eval ((x + y) ^ p) = g.eval (x ^ p) + g.eval (y ^ p) := by
    rw [← Polynomial.expand_eval, ← Polynomial.expand_eval, ← Polynomial.expand_eval]
    simpa [hfg] using h
  rw [hxy, hx, hy] at h'
  exact h'

omit [IsAlgClosed k] in
private lemma natDegree_contract_mul_degree
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hfder : f.derivative = 0) (hfne : f ≠ 0) :
    (Polynomial.contract p f).natDegree * p = f.natDegree := by
  have hexpand : Polynomial.expand k p (Polynomial.contract p f) = f :=
    Polynomial.expand_contract p hfder (Fact.out : p.Prime).ne_zero
  have hne : Polynomial.contract p f ≠ 0 := by
    intro hzero
    apply hfne
    rw [← hexpand, hzero, map_zero]
  rw [← Polynomial.natDegree_expand p (Polynomial.contract p f), hexpand]

/-- A nonzero additive polynomial has degree a power of the field characteristic. -/
public theorem additivePolynomial_natDegree_eq_ringChar_pow
    {f : Polynomial k} (hf : IsAdditivePolynomial f) (hne : f ≠ 0) :
    ∃ m : ℕ, f.natDegree = ringChar k ^ m := by
  by_cases hchar : ringChar k = 0
  · letI : CharP k 0 := ringChar.of_eq hchar
    letI : CharZero k := CharP.charP_to_charZero k
    exact ⟨0, by simpa [ringChar.eq_zero] using
      (additivePolynomial_natDegree_eq_one hf hne)⟩
  · let p : ℕ := ringChar k
    letI : CharP k p := by simpa [p] using (ringChar.charP k)
    have hpprime : p.Prime :=
      (CharP.char_is_prime_or_zero k p).resolve_right (by simpa [p] using hchar)
    letI : Fact p.Prime := ⟨hpprime⟩
    have hmain : ∀ n : ℕ, ∀ {f : Polynomial k}, f.natDegree = n →
        IsAdditivePolynomial f → f ≠ 0 → ∃ m : ℕ, f.natDegree = p ^ m := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro f hdeg hf hne
          obtain ⟨c, hc⟩ := additive_derivative_constant_degree f hf
          let g : Polynomial k := f - Polynomial.C c * Polynomial.X
          have hg : IsAdditivePolynomial g := additive_sub_linear_degree hf c
          have hgder : g.derivative = 0 := by
            dsimp [g]
            rw [Polynomial.derivative_sub, hc, Polynomial.derivative_C_mul,
              Polynomial.derivative_X]
            simp
          by_cases hgzero : g = 0
          · have hflin : f = Polynomial.C c * Polynomial.X := by
              dsimp [g] at hgzero
              exact sub_eq_zero.mp hgzero
            have hcne : c ≠ 0 := by
              intro hc0
              apply hne
              rw [hflin, hc0]
              simp
            refine ⟨0, ?_⟩
            rw [hflin, Polynomial.natDegree_C_mul_X c hcne, pow_zero]
          · have hgpos : 0 < g.natDegree := additive_natDegree_pos_degree hg hgzero
            let h : Polynomial k := Polynomial.contract p g
            have hh : IsAdditivePolynomial h := contract_additive_of_derivative_zero_degree hg hgder
            have hgne : h ≠ 0 := by
              intro hhzero
              apply hgzero
              have hexpand : Polynomial.expand k p h = g :=
                Polynomial.expand_contract p hgder (Fact.out : p.Prime).ne_zero
              rw [← hexpand, hhzero, map_zero]
            have hdegmul : h.natDegree * p = g.natDegree := by
              dsimp [h]
              exact natDegree_contract_mul_degree hgder hgzero
            have hpgt : 1 < p := hpprime.one_lt
            have hgnat_ge_two : 2 ≤ g.natDegree := by
              have hgneone : g.natDegree ≠ 1 := by
                intro hgone
                have hgcoeff : g.coeff 1 ≠ 0 := by
                  rw [← hgone, Polynomial.coeff_natDegree]
                  exact Polynomial.leadingCoeff_ne_zero.mpr hgzero
                have hdercoeff := congrArg (fun q : Polynomial k => q.coeff 0) hgder
                have hcoeffzero : g.coeff 1 = 0 := by
                  simpa [Polynomial.coeff_derivative] using hdercoeff
                exact hgcoeff hcoeffzero
              omega
            have hgle : g.natDegree ≤ n := by
              dsimp [g]
              apply le_trans (Polynomial.natDegree_sub_le _ _)
              apply max_le
              · exact hdeg.le
              · have hnpos : 0 < n := by
                  rw [← hdeg]
                  exact additive_natDegree_pos_degree hf hne
                exact (Polynomial.natDegree_C_mul_le c Polynomial.X).trans
                  (by simp [Polynomial.natDegree_X]; omega)
            have hhlt : h.natDegree < n := by
              have hhpos : 0 < h.natDegree := additive_natDegree_pos_degree hh hgne
              have hh_lt_g : h.natDegree < g.natDegree := by
                rw [← hdegmul]
                calc
                  h.natDegree < h.natDegree * 2 := by omega
                  _ ≤ h.natDegree * p := Nat.mul_le_mul_left _ (by omega)
              exact hh_lt_g.trans_le hgle
            obtain ⟨m, hm⟩ := ih h.natDegree hhlt rfl hh hgne
            have hglin : f = g + Polynomial.C c * Polynomial.X := by
              dsimp [g]
              abel
            have hlinlt : (Polynomial.C c * Polynomial.X).natDegree < g.natDegree := by
              have hcdeg : (Polynomial.C c * Polynomial.X).natDegree ≤ 1 := by
                exact (Polynomial.natDegree_C_mul_le c Polynomial.X).trans_eq
                  Polynomial.natDegree_X
              omega
            refine ⟨m + 1, ?_⟩
            rw [hglin, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlinlt]
            exact hdegmul.symm.trans (by rw [hm, pow_succ])
    exact hmain f.natDegree rfl hf hne

end Theory.AlgebraicGroup
