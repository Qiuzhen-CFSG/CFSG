module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual
public import CFSG.Quasithin.Chapter3.Section02.SourceXiSigns

/-!
# The prime restriction in 13.3.14(d)

An actual cubic automizer rules out the {2,5} alternative in Definition
3.2.12. A nontrivial odd p-group quotient then forces p=3. The residual
application uses the literal projection constructed in Residual, including
its embedding back into the original ambient group.

Membership in Ξ-minus remains a premise here: its construction needs the
source-adequate embedding alternative, the 13.3.2 list exclusion, and 3.2.13.
Neither an intrinsic Held exclusion nor original 1.3.4 is invoked.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14(d), printed p.892, PDF p.909; Definition 3.2.12, p.584.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A cubic ambient automizer excludes the {2,5} clause of Ξ-minus. -/
theorem prime_divisors_of_XiMinus_of_cubic_automizer {T P : Subgroup G}
    (hP : P ∈ Chapter3.XiMinus G T)
    (h3 : 3 ∣ Nat.card (Chapter3.xiQuotientAutomizer P)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card P → p = 2 ∨ p = 3 := by
  rcases hP.2 with h | h
  · exact h
  · rcases h.2 3 Nat.prime_three h3 with h | h <;> omega

omit [Finite G] in
/-- An odd nontrivial p-group quotient fixes the remaining prime as three. -/
theorem prime_eq_three_of_XiMinus_of_odd_quotient {T P : Subgroup G}
    (hP : P ∈ Chapter3.XiMinus G T)
    (h3 : 3 ∣ Nat.card (Chapter3.xiQuotientAutomizer P))
    {D : Type*} [Group D] [Finite D] [Nontrivial D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hD : IsPGroup p D)
    (f : P →* D) (hf : Function.Surjective f) : p = 3 := by
  obtain ⟨n, hn, he⟩ := hD.nontrivial_iff_card.mp inferInstance
  have hd : p ∣ Nat.card D := he ▸ dvd_pow_self p (by omega : n ≠ 0)
  have hc : Nat.card D ∣ Nat.card P := Subgroup.card_dvd_of_surjective f hf
  rcases prime_divisors_of_XiMinus_of_cubic_automizer hP h3 p Fact.out (hd.trans hc)
    with h2 | h3
  · obtain ⟨k, hk⟩ := hp
    omega
  · exact h3

/-- Use an actual ambient normalizer element as the cubic automizer witness. -/
theorem prime_eq_three_of_XiMinus_of_cubic_actor {T P : Subgroup G}
    (hP : P ∈ Chapter3.XiMinus G T)
    (x : normalizer (P : Set G))
    (hx : orderOf (Chapter3.xiQuotientNormalizerAction P x) = 3)
    {D : Type*} [Group D] [Finite D] [Nontrivial D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hD : IsPGroup p D)
    (f : P →* D) (hf : Function.Surjective f) : p = 3 :=
  prime_eq_three_of_XiMinus_of_odd_quotient hP
    (Chapter3.three_dvd_xiQuotientAutomizer_of_actor P x hx) hp hD f hf

/-- The prime restriction for the literal residual, embedded in the original group. -/
theorem prime_eq_three_of_starResidual_XiMinus
    (T H : Subgroup G) (D : Subgroup (Star H)) [Nontrivial D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hD : IsPGroup p D)
    (hminus : (starResidual H D).map H.subtype ∈ Chapter3.XiMinus G T)
    (h3 : 3 ∣ Nat.card (Chapter3.xiQuotientAutomizer ((starResidual H D).map H.subtype))) :
    p = 3 := by
  let e := (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
  let f := (starResidualProjection H D (odd_pGroup_isTwoPerfect hp hD)).comp
    e.symm.toMonoidHom
  exact prime_eq_three_of_XiMinus_of_odd_quotient hminus h3 hp hD f
    ((starResidualProjection_surjective H D (odd_pGroup_isTwoPerfect hp hD)).comp
      e.symm.surjective)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
