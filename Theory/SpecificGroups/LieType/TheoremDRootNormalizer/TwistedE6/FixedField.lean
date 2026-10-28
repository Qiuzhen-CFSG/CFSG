module

public import Theory.SpecificGroups.LieType.TwistedE6Field
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Fixed coefficients for the twisted E6 root normalizer

The parameters are the actual fixed subfield of q-Frobenius in GF(q²).
For q > 2, a prime divisor of q − 1 gives odd torsion in this subfield:
Cauchy's theorem is applied in GF(q²)ˣ, and the order equation proves
Frobenius fixation. In particular this subfield has more than two elements.
No identification with a separately constructed finite field is needed.

This supplies the coefficient input for the torus obstruction used in
Aschbacher–Smith A.2.18 (printed p.40), on the pinned carrier of
GLS3 §§2.2–2.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6.TheoremDRootNormalizer
noncomputable section

def fixedField (m : ℕ) : Subfield (CoefficientField 2 m) :=
  (fieldTwist 2 m).toRingHom.eqLocusField (RingHom.id _)

abbrev FixedField (m : ℕ) := ↥(fixedField m)

@[simp] theorem fixedField_pow (m : ℕ) (t : FixedField m) :
    (t : CoefficientField 2 m) ^ parameter 2 m = t := t.property

theorem parameter_gt_two (m : ℕ) (hm : 0 < m) : 2 < parameter 2 m := by
  change 2 < 2 ^ (m + 1)
  have h := Nat.pow_lt_pow_right (a := 2) (by omega) (show 1 < m + 1 by omega)
  simpa using h

theorem exists_fixed_prime (m : ℕ) (hm : 0 < m) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ Nat.card (rootsOfUnity p (FixedField m)) = p := by
  have hq := parameter_gt_two m hm
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show parameter 2 m - 1 ≠ 1 by omega)
  have he : Even (parameter 2 m) := by
    unfold parameter
    rw [pow_succ]
    exact even_two.mul_left _
  have ho : Odd p := hp.odd_of_ne_two (by
    intro h
    subst p
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hd
    omega)
  have hdu : p ∣ Nat.card (CoefficientField 2 m)ˣ := by
    rw [Nat.card_units, field_card]
    have hfac : parameter 2 m ^ 2 - 1 = (parameter 2 m - 1) * (parameter 2 m + 1) := by
      have hpos := parameter_ge_two 2 m
      have hsub : parameter 2 m - 1 + 1 = parameter 2 m := by omega
      have hprod : (parameter 2 m - 1) * (parameter 2 m + 1) + 1 = parameter 2 m ^ 2 := by nlinarith
      omega
    rw [hfac]
    exact dvd_mul_of_dvd_left hd _
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (CoefficientField 2 m)ˣ) p hdu
  have hpow : u ^ (parameter 2 m - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hu ▸ hd)
  have hfix : (u : CoefficientField 2 m) ^ parameter 2 m = u := by
    have hq1 : parameter 2 m = (parameter 2 m - 1) + 1 := by omega
    rw [hq1, pow_succ]
    have heq := congrArg Units.val hpow
    rw [show (u : CoefficientField 2 m) ^ (parameter 2 m - 1) = 1 from heq, one_mul]
  let a : FixedField m := ⟨u, hfix⟩
  have ha : a ≠ 0 := by
    intro h
    exact u.ne_zero (congrArg Subtype.val h)
  let v : (FixedField m)ˣ := Units.mk0 a ha
  have hv : Units.map (fixedField m).subtype.toMonoidHom v = u := Units.ext rfl
  have hinj : Function.Injective (Units.map (fixedField m).subtype.toMonoidHom) := by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val h
  have hvorder : orderOf v = p := by
    rw [← hv, orderOf_injective _ hinj] at hu
    exact hu
  let : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨p, hp, ho, (hvorder ▸ IsPrimitiveRoot.orderOf v).card_rootsOfUnity'⟩

theorem fixedField_card_gt_two (m : ℕ) (hm : 0 < m) : 2 < Nat.card (FixedField m) := by
  obtain ⟨p, hp, ho, hc⟩ := exists_fixed_prime m hm
  have hbound := Nat.card_le_card_of_injective
    (rootsOfUnity p (FixedField m)).subtype Subtype.val_injective
  rw [hc, Nat.card_units] at hbound
  have hp2 := hp.two_le
  obtain ⟨a, ha⟩ := ho
  omega

end
end TwistedE6.TheoremDRootNormalizer
