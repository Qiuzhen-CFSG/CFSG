module
public import Mathlib.GroupTheory.PGroup

/-!
# No factor eleven in automorphisms of a group of order thirty-two

No subgroup of the automorphism group of a finite group of order 32 has
order divisible by 11. Neither commutativity nor solvability is needed.
Cauchy supplies an automorphism of order 11. Orbit counting makes the fixed
subgroup order congruent to 32 modulo 11, while Lagrange makes it a power of
two dividing 32. Only 32 satisfies this congruence, so every element is fixed.

This elementary counting argument supplies the first excessive-order
exclusion in Parrott (1972), Lemma 2, p.673, without computing GL(5,2).
-/

public theorem not_eleven_dvd_card_automorphism_thirtytwo
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 32)
    (K : Subgroup (MulAut E)) : ¬ 11 ∣ Nat.card K := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro hdiv
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 11 hdiv
  let A := Subgroup.zpowers (a : MulAut E)
  have hA : Nat.card A = 11 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hgroup : IsPGroup 11 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hgroup.card_modEq_card_fixedPoints E
  change Nat.ModEq 11 (Nat.card E) (Nat.card (FixedPoints.subgroup A E)) at hmod
  have hdivC : Nat.card (FixedPoints.subgroup A E) ∣ 2 ^ 5 := by
    simpa [hE] using (FixedPoints.subgroup A E).card_subgroup_dvd_card
  obtain ⟨n, hn, hCn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdivC
  have hC : Nat.card (FixedPoints.subgroup A E) = 32 := by
    rw [hE, hCn] at hmod
    interval_cases n <;> norm_num [Nat.ModEq] at hmod
    simpa using hCn
  have htop : FixedPoints.subgroup A E = ⊤ := Subgroup.eq_top_of_card_eq _ (hC.trans hE.symm)
  have ha1 : (a : MulAut E) = 1 := by
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup A E := htop ▸ Subgroup.mem_top x
    exact hx ⟨a, Subgroup.mem_zpowers (a : MulAut E)⟩
  have ha' : a = 1 := Subtype.ext ha1
  simp [ha'] at ha
