module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction.SideMarkers
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Recover binary Ree digits from the finite highest characters

Binary sums lie below the coefficient-field cardinality. Equality on the
nonzero field elements, together with agreement on whether the whole digit
column vanishes, extends to equality of the corresponding monomial functions
on the whole field. The polynomial root bound identifies their exponents;
uniqueness of binary expansion identifies every digit. This explicitly
handles the zero/full-column ambiguity of torus characters, also at q=2.

Source: Steinberg (1963), 5.1(4) and 12.2.
-/

public section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction

private def binaryValue (b : ℕ → ℕ) (n : ℕ) : ℕ := ∑i∈Finset.range n, 2^i * b i

private theorem binaryValue_lt (b : ℕ → ℕ) (hb : ∀i, b i < 2) (n : ℕ) : binaryValue b n < 2^n := by
  induction n with
  | zero => simp [binaryValue]
  | succ n ih =>
    change (∑i∈Finset.range (n+1), 2^i * b i) < _
    rw [Finset.sum_range_succ,pow_succ]
    change binaryValue b n + 2^n * b n < _
    have h := hb n
    have hp : 0 < 2^n := by positivity
    have hh : b n = 0 ∨ b n = 1 := by omega
    rcases hh with hz | hz <;> rw [hz] <;> simp only [mul_zero,mul_one] <;> omega

private theorem binaryValue_injective (b c : ℕ → ℕ) (hb : ∀i,b i<2) (hc : ∀i,c i<2)
    (n : ℕ) (he : binaryValue b n = binaryValue c n) : ∀i<n, b i = c i := by
  induction n with
  | zero => omega
  | succ n ih =>
    have he' : binaryValue b n + 2^n * b n = binaryValue c n + 2^n * c n := by
      simpa only [binaryValue,Finset.sum_range_succ] using he
    have ht : binaryValue b n = binaryValue c n := by
      have hh := congrArg (fun a : ℕ => a % (2^n)) he'
      simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
        Nat.mod_eq_of_lt (binaryValue_lt b hb n), Nat.mod_eq_of_lt (binaryValue_lt c hc n)] using hh
    have hn : b n = c n := by
      rw [ht] at he'
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0<2^n) (Nat.add_left_cancel he')
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl
    · exact ih ht i hil
    · exact hn

theorem side_digits_of_characters {F : Type*} [Field F] (m : ℕ)
    (f : CoefficientField m →+* F) (b c : ℕ → BasicWeight) (s : LargeLocalSeeds.Side)
    (ht : ∀t : (CoefficientField m)ˣ,
      (f t)^(∑i∈Finset.range (2*m+1),2^i * sideDigit s (b i)) =
      (f t)^(∑i∈Finset.range (2*m+1),2^i * sideDigit s (c i)))
    (hz : (∀i<2*m+1,sideDigit s (b i)=0) ↔ ∀i<2*m+1,sideDigit s (c i)=0) :
    ∀i<2*m+1,sideDigit s (b i)=sideDigit s (c i) := by
  let A := binaryValue (fun i=>sideDigit s (b i)) (2*m+1)
  let D := binaryValue (fun i=>sideDigit s (c i)) (2*m+1)
  have hb (i : ℕ) : sideDigit s (b i) < 2 := by cases s <;> exact Fin.isLt _
  have hc (i : ℕ) : sideDigit s (c i) < 2 := by cases s <;> exact Fin.isLt _
  have hzero (a : ℕ→BasicWeight) : binaryValue (fun i=>sideDigit s (a i)) (2*m+1)=0 ↔
      ∀i<2*m+1,sideDigit s (a i)=0 := by
    simp only [binaryValue, Finset.sum_eq_zero_iff, Finset.mem_range]
    apply forall₂_congr
    intro i hi
    simp only [mul_eq_zero, pow_ne_zero _ (by decide : (2:ℕ)≠0), false_or]
  have hAD : (A=0 ↔ D=0) := (hzero b).trans (hz.trans (hzero c).symm)
  have hp : (Polynomial.X^A - Polynomial.X^D : Polynomial F)=0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ f.injective
    · intro t
      simp only [Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,sub_eq_zero]
      by_cases ht0 : t=0
      · subst t
        rw [map_zero]
        by_cases hA : A=0
        · rw [hA,hAD.mp hA]
        · rw [zero_pow hA,zero_pow (mt hAD.mpr hA)]
      · exact ht (Units.mk0 t ht0)
    · have hdeg := Polynomial.natDegree_sub_le (Polynomial.X^A : Polynomial F) (Polynomial.X^D)
      simp only [Polynomial.natDegree_X_pow] at hdeg
      apply lt_of_le_of_lt hdeg
      rw [←Nat.card_eq_fintype_card,field_card]
      exact max_lt (binaryValue_lt _ hb _) (binaryValue_lt _ hc _)
  have he : A=D := by
    have hh := congrArg Polynomial.natDegree (sub_eq_zero.mp hp)
    simpa only [Polynomial.natDegree_X_pow] using hh
  exact binaryValue_injective _ _ hb hc _ he

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
