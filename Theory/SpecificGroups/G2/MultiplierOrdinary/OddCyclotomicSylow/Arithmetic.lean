module

public import Theory.AtlasPort.LinearGroups.G2.Order
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The two cyclotomic torus indices in G₂

Factoring the checked order q⁶(q⁶ − 1)(q² − 1) gives the index of any
actual subgroup of order q² + q + 1 or q² − q + 1. The two factors cannot
share a prime greater than three. A cyclic subgroup of the relevant order
therefore contains a full Sylow subgroup at a nondefining prime missing
q² − 1; Sylow conjugacy gives cyclicity of every such Sylow subgroup.

The subgroup itself remains a geometric input. `CubicTorus` constructs the
first one, and the main `OddCyclotomicSylow` module applies the result to
the canonical perfect central cover. These arithmetic and group-theoretic
steps do not establish the existence of either torus by themselves.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1. The actual model order is the attributed ATLAS port.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow

private theorem sixth_factorization (q : ℕ) (hq : 1 ≤ q) :
    q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub (Nat.one_le_pow 6 q hq),
    Nat.cast_sub (Nat.one_le_pow 2 q hq), Nat.cast_sub hq2]
  ring

/-- The checked model order, factored into its two cubic cyclotomic factors. -/
theorem card_model_factorization {F : Type*} [Field F] [Finite F] :
    Nat.card (Model F) = Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) ^ 2 *
      (Nat.card F ^ 2 + Nat.card F + 1) * (Nat.card F ^ 2 - Nat.card F + 1) := by
  rw [card_Model, sixth_factorization _ Nat.card_pos]
  ring

private theorem cyclotomic_disjoint {q r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (h3 : r ∣ q ^ 2 + q + 1) : ¬ r ∣ q ^ 2 - q + 1 := by
  intro h6
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have h3' := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr h3
  have h6' := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr h6
  push_cast [Nat.cast_sub hq2] at h3' h6'
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have hd : r ∣ 2 := (CharP.cast_eq_zero_iff (ZMod r) r 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hx : (2 : ZMod r) * (q : ZMod r) = 0 := by
    linear_combination h3' - h6'
  have hq : (q : ZMod r) = 0 := (mul_eq_zero.mp hx).resolve_left h2
  simp [hq] at h3'

/-- Every source prime outside p(p² − 1) divides one of the two torus orders. -/
theorem cyclotomic_alternatives {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1) (horder : r ∣ Nat.card (Model F)) :
    r ∣ p ^ 2 + p + 1 ∨ r ∣ p ^ 2 - p + 1 := by
  rw [card_model_factorization, hF] at horder
  have hr := (Fact.out : r.Prime)
  have hnp : ¬ r ∣ p := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hr Fact.out).mp h)
  have hn : ¬ r ∣ p ^ 6 * (p ^ 2 - 1) ^ 2 :=
    hr.not_dvd_mul (fun h => hnp (hr.dvd_of_dvd_pow h))
      (fun h => hquad (hr.dvd_of_dvd_pow h))
  rcases hr.dvd_mul.mp horder with h | h
  · exact Or.inl ((hr.dvd_mul.mp h).resolve_left hn)
  · exact Or.inr h

/-- The index of an actual subgroup with cubic cyclotomic cardinality. -/
theorem index_of_cubic_card {F : Type*} [Field F] [Finite F]
    (C : Subgroup (Model F)) (hc : Nat.card C = Nat.card F ^ 2 + Nat.card F + 1) :
    C.index = Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) ^ 2 *
      (Nat.card F ^ 2 - Nat.card F + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 2 + Nat.card F + 1 by omega)
  rw [← hc, C.card_mul_index, card_model_factorization, hc]
  ring

/-- The index of an actual subgroup with twisted cubic cyclotomic cardinality. -/
theorem index_of_twisted_cubic_card {F : Type*} [Field F] [Finite F]
    (C : Subgroup (Model F)) (hc : Nat.card C = Nat.card F ^ 2 - Nat.card F + 1) :
    C.index = Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) ^ 2 *
      (Nat.card F ^ 2 + Nat.card F + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 2 - Nat.card F + 1 by omega)
  rw [← hc, C.card_mul_index, card_model_factorization, hc]
  ring

private theorem sylow_isCyclic_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (hi : ¬ r ∣ C.index) (Q : Sylow r G) : IsCyclic Q := by
  let T : Sylow r C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup r A := T.isPGroup'.map C.subtype
  have hai : ¬ r ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul T.not_dvd_index hi
  let U : Sylow r G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv Q).isCyclic.mp hc

/-- An actual cyclic cubic torus contains a Sylow subgroup at the source prime. -/
theorem sylow_isCyclic_of_cubic_torus {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (hd : r ∣ p ^ 2 + p + 1)
    (C : Subgroup (Model F)) [IsCyclic C] (hc : Nat.card C = p ^ 2 + p + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  apply sylow_isCyclic_of_cyclic_index C ?_ Q
  rw [index_of_cubic_card C (by simpa only [hF] using hc), hF]
  have hp := (Fact.out : r.Prime)
  apply hp.not_dvd_mul
  · apply hp.not_dvd_mul
    · intro h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp (hp.dvd_of_dvd_pow h))
    · exact fun h => hquad (hp.dvd_of_dvd_pow h)
  · exact cyclotomic_disjoint hr hd

/-- An actual cyclic twisted cubic torus contains a Sylow subgroup at the source prime. -/
theorem sylow_isCyclic_of_twisted_cubic_torus {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (hd : r ∣ p ^ 2 - p + 1)
    (C : Subgroup (Model F)) [IsCyclic C] (hc : Nat.card C = p ^ 2 - p + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  apply sylow_isCyclic_of_cyclic_index C ?_ Q
  rw [index_of_twisted_cubic_card C (by simpa only [hF] using hc), hF]
  have hp := (Fact.out : r.Prime)
  apply hp.not_dvd_mul
  · apply hp.not_dvd_mul
    · intro h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp (hp.dvd_of_dvd_pow h))
    · exact fun h => hquad (hp.dvd_of_dvd_pow h)
  · intro h3
    exact cyclotomic_disjoint hr h3 hd

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow
