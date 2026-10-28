module

public import Theory.Representation.BinaryEightPrimeObstruction
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.Models

/-!
# The order sieve in G.7.2 for odd linear groups

Aschbacher--Smith, combined 1 March 2004 manuscript, printed pp.347--348,
G.7.2(2),(3). The general linear group order bounds the defining prime and
its exponent. The PSL order formula then excludes the remaining powers of
three, leaving the four Frobenius cases and the parameter seventeen.
Seventeen forces degree at least eight. In dimension three, the defining
prime cube divides the projective group order; in binary degree at most eight
this forces prime three, which is excluded by the prime divisor thirteen.

These statements use actual matrix-model equivalences. They do not require
irreducibility or SQTK. The four Frobenius exclusions and the irreducible
PSU3(3) assertion remain separate obligations in the source theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

open Matrix Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups
private theorem exponent_lt {p e b N : ℕ} (h : p ^ e ∣ N) (hb : ¬ p ^ b ∣ N) :
    e < b := by
  by_contra he
  exact hb ((Nat.pow_dvd_pow p (by omega)).trans h)

private theorem arithmetic_sieve {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e)
    (h : p ^ e * ((p ^ e) ^ 2 - 1) ∣ Nat.card (GL (Fin 8) (ZMod 2)) * 2) :
    p ^ e ≤ 9 ∨ p ^ e = 17 ∨ p ^ e = 25 ∨ p ^ e = 49 ∨
      p ^ e = 31 ∨ p ^ e = 127 := by
  have hpow : p ^ e ∣ Nat.card (GL (Fin 8) (ZMod 2)) * 2 :=
    (dvd_mul_right _ _).trans h
  have hpdiv : p ∣ Nat.card (GL (Fin 8) (ZMod 2)) := by
    apply (hp.coprime_iff_not_dvd.mpr (by
      intro hd
      exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one))).dvd_of_dvd_mul_right
    exact (dvd_pow_self p (by omega)).trans hpow
  have hpList := Representation.BinaryEight.prime_divisors_binary_GL_eight hp hpdiv
  rw [Matrix.card_GL_field] at hpow h
  norm_num [Fin.prod_univ_succ] at hpow h
  rcases hpList with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hp2 rfl).elim
  · have heb := exponent_lt hpow (by norm_num : ¬ 3 ^ 6 ∣ 10696127538423398400)
    interval_cases e <;> norm_num at *
  · have heb := exponent_lt hpow (by norm_num : ¬ 5 ^ 3 ∣ 10696127538423398400)
    interval_cases e <;> norm_num at *
  · have heb := exponent_lt hpow (by norm_num : ¬ 7 ^ 3 ∣ 10696127538423398400)
    interval_cases e <;> norm_num at *
  · have heb := exponent_lt hpow (by norm_num : ¬ 17 ^ 2 ∣ 10696127538423398400)
    interval_cases e
    norm_num
  · have heb := exponent_lt hpow (by norm_num : ¬ 31 ^ 2 ∣ 10696127538423398400)
    interval_cases e
    norm_num
  · have heb := exponent_lt hpow (by norm_num : ¬ 127 ^ 2 ∣ 10696127538423398400)
    interval_cases e
    norm_num

/-- The precise remaining PSL2 parameters before the Frobenius exclusions. -/
theorem psl2_parameter_sieve {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL G 2 (p ^ e))
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    p ^ e ≤ 9 ∨ p ^ e = 17 ∨ p ^ e = 25 ∨ p ^ e = 49 ∨
      p ^ e = 31 ∨ p ^ e = 127 := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  have horder : Nat.card G * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [Nat.card_congr f.toEquiv]
    simpa only [hcard] using psl2_card_twice (F := F) (hcard ▸ ho.pow)
  apply arithmetic_sieve hp (by rintro rfl; norm_num at ho) he
  rw [← horder]
  exact Nat.mul_dvd_mul_right
    ((Representation.card_dvd_card_GL_of_injective ρ hρ).trans
      (Representation.BinaryEight.card_binary_GL_dvd_eight hd)) 2

/-- Only the odd prime three can occur to its third power in the binary GL8 order. -/
theorem prime_eq_three_of_cube_dvd_GL8 {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (h : p ^ 3 ∣ Nat.card (GL (Fin 8) (ZMod 2))) : p = 3 := by
  have hpdiv := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have hpList := Representation.BinaryEight.prime_divisors_binary_GL_eight hp hpdiv
  rw [Matrix.card_GL_field] at h
  norm_num [Fin.prod_univ_succ] at h
  rcases hpList with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The parameter twenty-five is already excluded by its prime divisor
thirteen; its Borel Frobenius subgroup is not needed for this exclusion. -/
theorem psl2_twentyFive_degree_ge_twelve (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSL G 2 25) :
    12 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  have hc := psl2_card_twice (F := F) (hcard ▸ (by decide : Odd 25))
  rw [← Nat.card_congr f.toEquiv, hcard] at hc
  have hd : 13 ∣ Nat.card G := by
    have hcardG : Nat.card G = 7800 := by omega
    rw [hcardG]
    norm_num
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ (by decide : Nat.Prime 13)
      (by decide) hd

/-- The order sieve after removing twenty-five by the prime thirteen.
Only the three parameters 49, 31 and 127 still require local exclusions. -/
theorem psl2_parameter_sieve_refined (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL G 2 (p ^ e))
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    p ^ e ≤ 9 ∨ p ^ e = 17 ∨ p ^ e = 49 ∨ p ^ e = 31 ∨ p ^ e = 127 := by
  have h25 : p ^ e ≠ 25 := by
    intro h
    have := psl2_twentyFive_degree_ge_twelve ρ hρ (h ▸ hmodel)
    omega
  rcases psl2_parameter_sieve ρ hρ hp ho he hmodel hd with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact (h25 h).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The surviving PSL2(17) parameter cannot have binary degree at most six. -/
theorem psl2_seventeen_degree_ge_eight (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSL G 2 17) :
    8 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  have hc := psl2_card_twice (F := F) (hcard ▸ (by decide : Odd 17))
  rw [← Nat.card_congr f.toEquiv, hcard] at hc
  have hd : 17 ∣ Nat.card G := by
    have hcardG : Nat.card G = 2448 := by omega
    rw [hcardG]; norm_num
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_seventeen] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ (by decide : Nat.Prime 17)
      (by decide) hd

/-- The prime thirteen excludes PSL3(3) below binary degree twelve. -/
theorem psl3_three_degree_ge_twelve (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSL G 3 3) :
    12 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  have hd : 13 ∣ Nat.card G := by
    rw [Nat.card_congr f.toEquiv]
    exact thirteen_dvd_card_psl3 hcard
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ (by decide : Nat.Prime 13)
      (by decide) hd

/-- The projective linear branch of G.7.2(3) is impossible in degree at most eight. -/
theorem psl3_degree_gt_eight (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL G 3 p) : 8 < Module.finrank (ZMod 2) V := by
  by_contra! hd
  have hdiv : p ^ 3 ∣ Nat.card G := by
    obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
    rw [Nat.card_congr f.toEquiv, ← hcard]
    exact psl3_cube_dvd_card
  have hp3 := prime_eq_three_of_cube_dvd_GL8 hp ho
    (hdiv.trans ((Representation.card_dvd_card_GL_of_injective ρ hρ).trans
      (Representation.BinaryEight.card_binary_GL_dvd_eight hd)))
  subst p
  have := psl3_three_degree_ge_twelve ρ hρ hmodel
  omega

/-- The special linear alternative is excluded as well: the projective
order divides the special order, even when the action does not descend. -/
theorem sl3_degree_gt_eight (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : IsSLThree G p) : 8 < Module.finrank (ZMod 2) V := by
  by_contra! hd
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  have hquot : Nat.card PSL(3,F) ∣ Nat.card G := by
    rw [Nat.card_congr f.toEquiv]
    exact Subgroup.card_quotient_dvd_card (Subgroup.center SL(3,F))
  have hdiv : p ^ 3 ∣ Nat.card G := by
    rw [← hcard]
    exact psl3_cube_dvd_card.trans hquot
  have hp3 := prime_eq_three_of_cube_dvd_GL8 hp ho
    (hdiv.trans ((Representation.card_dvd_card_GL_of_injective ρ hρ).trans
      (Representation.BinaryEight.card_binary_GL_dvd_eight hd)))
  have h13 := (thirteen_dvd_card_psl3 (hcard.trans hp3)).trans hquot
  have := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
    (by decide : Nat.Prime 13) (by decide) h13
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen] at this
  omega

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
