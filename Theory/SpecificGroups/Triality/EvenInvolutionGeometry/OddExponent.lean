module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.FieldTheory.OddQuadraticCoefficientLift
public import Theory.GroupAction.SylowPointwiseInner

/-!
# Two-power automorphisms at odd triality field exponent

The coefficient field is GF(2^(3n)), whose automorphism group has order 3n.
For odd n its image in the outer group has odd order. Thus an automorphism
of two-power order expressed as inner times coefficient is inner. This
includes n = 1 and requires no restriction to involutions or Sylow hypothesis.
The inner–coefficient expression is the sole model-automorphism premise;
its global coverage is supplied separately.

This proves the odd-exponent innerness part used in Aschbacher–Smith 16.1.6,
printed p.1172 (`refs/quasithin.pdf`); coefficient conventions are GLS3 §2.5.
-/

public section
noncomputable section
namespace Triality.Standard.EvenInvolutionGeometry
open OuterOdd

/-- The order-three contribution from the cubic field is retained at n = 1. -/
theorem coefficientAut_card (n : ℕ) (hn : 0 < n) :
    Nat.card (CoefficientAut (binaryParameters n hn)) = 3 * n :=
  GaloisField.card_ringAut 2 (3 * n) (by omega)

/-- At odd exponent, every two-power automorphism with the source
inner–coefficient expression is inner. -/
theorem inner_of_odd_exponent (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (a : MulAut (BinaryCarrier n hn)) {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hform : ∃ g : BinaryCarrier n hn,
      ∃ e : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    ∃ g : BinaryCarrier n hn, a = MulAut.conj g := by
  let I := (MulAut.conj : BinaryCarrier n hn →* MulAut (BinaryCarrier n hn)).range
  let q := QuotientGroup.mk' I
  obtain ⟨g, e, hform⟩ := hform
  have hq : q a = q (coefficientAction (binaryParameters n hn) e) := by
    rw [hform, map_mul, show q (MulAut.conj g) = 1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩, one_mul]
  have he : e ^ (3 * n) = 1 := by
    rw [← coefficientAut_card n hn]
    exact pow_card_eq_one'
  have hoddpow : (q a) ^ (3 * n) = 1 := by
    rw [hq, ← map_pow, ← map_pow, he, map_one, map_one]
  have htwopow : (q a) ^ (2 ^ k) = 1 := by rw [← map_pow, ha, map_one]
  have horder : orderOf (q a) = 1 := by
    apply Nat.eq_one_of_dvd_coprimes
      (((show Odd (3 * n) from (by decide : Odd 3).mul hodd).coprime_two_right).pow_right k)
      (orderOf_dvd_of_pow_eq_one hoddpow) (orderOf_dvd_of_pow_eq_one htwopow)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp horder)
  exact ⟨x, hx.symm⟩

/-- A non-inner two-power actor forces a genuine smaller binary exponent. -/
theorem exists_half_exponent_of_noninner (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hform : ∃ g : BinaryCarrier n hn,
      ∃ e : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (houter : ¬ ∃ g : BinaryCarrier n hn, a = MulAut.conj g) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m := by
  have heven : Even n := by
    rcases Nat.even_or_odd n with h | h
    · exact h
    · exact False.elim (houter (inner_of_odd_exponent n hn h a ha hform))
  obtain ⟨m, hm⟩ := heven
  exact ⟨m, by omega, by omega⟩

end Triality.Standard.EvenInvolutionGeometry
