module

public import Stellmacher.Recognition.Parrott.CosetSelection

/-!
# Power bounds for lifts of quotient order four

Put H=C_G(z), J=O₂(H), and DH=J′ as a subgroup of H. The elementary
structures of J/J′ and J′ imply that J has exponent dividing four.
Consequently every lift of an element of order four in H/J has order
dividing sixteen.

If such a lift has eighth power one but fourth power outside DH, its
actual order is eight and its fourth power is a core involution outside
DH. The involution-coset theorem then gives centralizer index five in
H/DH. These are necessary conditions for the remaining eighth-power
obstruction; this module does not yet exclude that case.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
the core structure on pp.673–674 and the involution-coset argument in
Lemma 4 on p.675.
-/

open Subgroup
namespace Stellmacher.Recognition

/-- The elementary derived subgroup and abelianization give exponent at
most four for the actual two-core. -/
public theorem parrott_core_fourth_power_eq_one
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    ∀ b : pCore 2 (centralizer ({z} : Set G)), b ^ 4 = 1 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let : IsElementaryAbelian 2 D :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 (J ⧸ D) :=
    (parrott_core_abelianization_structure z h).1
  intro b
  have hb : b ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff (N := D) _).mp
    change QuotientGroup.mk' D (b ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (J ⧸ D)) _
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (b ^ 2) hb
  simpa only [← pow_mul] using hh

/-- Quotient order four bounds the actual lift order by sixteen; it does
not identify the actual order with the quotient order. -/
public theorem parrott_outer_four_order_dvd_sixteen
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ y : H, orderOf (QuotientGroup.mk' J y) = 4 → orderOf y ∣ 16 := by
  intro H J y hy
  have hyJ : y ^ 4 ∈ J := by
    apply (QuotientGroup.eq_one_iff (N := J) _).mp
    change QuotientGroup.mk' J (y ^ 4) = 1
    rw [map_pow, ← hy]
    exact pow_orderOf_eq_one _
  have hh := congrArg J.subtype
    (parrott_core_fourth_power_eq_one z h ⟨y ^ 4, hyJ⟩)
  change (y ^ 4) ^ 4 = 1 at hh
  apply orderOf_dvd_of_pow_eq_one
  simpa only [← pow_mul] using hh

/-- A counterexample to the eighth-power obstruction must be an element
of actual order eight whose fourth power selects an involutory five-coset
orbit. The conclusion keeps that fourth power as the original element. -/
public theorem parrott_outer_four_bad_eighth_power_data
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ y : H, orderOf (QuotientGroup.mk' J y) = 4 → y ^ 8 = 1 →
      y ^ 4 ∉ DH →
      orderOf y = 8 ∧ y ^ 4 ∈ J ∧ orderOf (y ^ 4) = 2 ∧
        (centralizer ({QuotientGroup.mk' DH (y ^ 4)} : Set (H ⧸ DH))).index = 5 := by
  intro H J DH y hy hy8 hyD
  have hyJ : y ^ 4 ∈ J := by
    apply (QuotientGroup.eq_one_iff (N := J) _).mp
    change QuotientGroup.mk' J (y ^ 4) = 1
    rw [map_pow, ← hy]
    exact pow_orderOf_eq_one _
  have hy4ne : y ^ 4 ≠ 1 := fun hh => hyD (hh ▸ DH.one_mem)
  have hy4order : orderOf (y ^ 4) = 2 := orderOf_eq_prime
    (by simpa only [← pow_mul] using hy8) hy4ne
  have hyorder : orderOf y = 8 := by
    have hd : orderOf y ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hy8
    obtain ⟨n, hn, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [orderOf_pow, heq] at hy4order
    interval_cases n <;> norm_num at hy4order
    exact heq
  exact ⟨hyorder, hyJ, hy4order,
    parrott_core_involution_coset_centralizer_index z h (y ^ 4) hyJ hy4order hyD⟩

end Stellmacher.Recognition
