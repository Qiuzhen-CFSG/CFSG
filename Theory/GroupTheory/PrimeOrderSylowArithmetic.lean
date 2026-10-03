module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Transfer
public import Lean.Elab.Tactic.Omega

/-!
# Arithmetic for Sylow subgroups of prime order

An exact prime divisor of the group order gives a Sylow subgroup of that
prime order. Its automizer divides `p - 1`, and Sylow's congruence converts
the order of its normalizer into a congruence for `|G| / p`.

Source: the elementary Sylow calculations in Alperin--Brauer--Gorenstein,
III.8, equations (9)--(11), article p.116.
-/

namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- A prime occurring just once in the group order is the Sylow order. -/
public theorem card_eq_prime_of_dvd_of_not_sq_dvd (P : Sylow p G)
    (hd : p ∣ Nat.card G) (hsq : ¬ p ^ 2 ∣ Nat.card G) : Nat.card P = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hpos : n ≠ 0 := by
    intro h
    have hdiv := P.dvd_card_of_dvd_card hd
    rw [hn, h, pow_zero] at hdiv
    exact hp.out.not_dvd_one hdiv
  have hlt : n < 2 := by
    by_contra h
    exact hsq ((hn.symm ▸ Nat.pow_dvd_pow p (by omega : 2 ≤ n)).trans
      P.toSubgroup.card_subgroup_dvd_card)
  have he : n = 1 := by omega
  simpa [he] using hn

/-- Conjugation embeds the automizer of a prime-order Sylow subgroup into
the automorphism group of a cyclic group of order `p`. -/
public theorem centralizer_relIndex_normalizer_dvd_prime_sub_one
    (P : Sylow p G) (hP : Nat.card P = p) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ∣ p - 1 := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  have h := card_dvd_of_injective _
    (QuotientGroup.kerLift_injective (P : Subgroup G).normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex, IsCyclic.card_mulAut,
    hP, Nat.totient_prime hp.out] at h
  exact h

omit hp in
/-- A Sylow subgroup of order `p` has odd centralizer when no involution
centralizer has order divisible by `p`. -/
public theorem not_two_dvd_centralizer_card (P : Sylow p G) (hP : Nat.card P = p)
    (hInv : ∀ t : G, orderOf t = 2 →
      ¬ p ∣ Nat.card (centralizer ({t} : Set G))) :
    ¬ 2 ∣ Nat.card (centralizer (P : Set G)) := by
  intro h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h
  have ht' : orderOf (t : G) = 2 := by simpa using ht
  have hle : (P : Subgroup G) ≤ centralizer ({(t : G)} : Set G) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    exact mem_centralizer_iff.mp t.property y hy
  apply hInv t ht'
  simpa only [hP] using card_dvd_of_le hle

omit [Finite G] hp in
/-- For a self-centralizing Sylow subgroup of order `p`, its normalizer
order is `p` times its automizer. -/
public theorem normalizer_card_of_self_centralizing (P : Sylow p G)
    (hP : Nat.card P = p) (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    Nat.card (normalizer (P : Set G)) = p *
      (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) := by
  have h := ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).index_mul_card
  have hle : (P : Subgroup G) ≤ normalizer (P : Set G) := le_normalizer
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hP] at h
  rw [hC, mul_comm]
  exact h.symm

/-- Burnside transfer excludes a trivial automizer in a simple group whose
order is larger than its prime-order Sylow subgroup. -/
public theorem centralizer_relIndex_normalizer_ne_one_of_simple [IsSimpleGroup G]
    (P : Sylow p G) (hP : Nat.card P = p) (hG : Nat.card G ≠ p) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ≠ 1 := by
  intro h
  have hn : normalizer (P : Set G) ≤ centralizer (P : Set G) := relIndex_eq_one.mp h
  have hk := MonoidHom.ker_transferSylow_isComplement' P hn
  have hprod := hk.card_mul_card
  rw [hP] at hprod
  rcases (inferInstance : (MonoidHom.transferSylow P hn).ker.Normal).eq_bot_or_eq_top with he | he
  · rw [he, card_bot, one_mul] at hprod
    exact hG hprod.symm
  · rw [he, card_top] at hprod
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
      (by simpa using hprod)
    exact hp.out.ne_one hp1

omit hp in
/-- In a simple group of order different from eleven, an odd automizer of
a Sylow subgroup of order eleven has order five. -/
public theorem centralizer_relIndex_normalizer_eq_five_of_odd [IsSimpleGroup G]
    (P : Sylow 11 G) (hP : Nat.card P = 11) (hG : Nat.card G ≠ 11)
    (ho : Odd ((centralizer (P : Set G)).relIndex (normalizer (P : Set G)))) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 5 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hd : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ∣ 10 :=
    P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have hn := P.centralizer_relIndex_normalizer_ne_one_of_simple hP hG
  have arith : ∀ m : Fin 11, m.val ∣ 10 → Odd m.val → m.val ≠ 1 → m.val = 5 := by decide
  exact arith ⟨_, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)⟩ hd ho hn

omit hp in
/-- In a simple group of order different from thirteen, an odd automizer
of a Sylow subgroup of order thirteen has order three. -/
public theorem centralizer_relIndex_normalizer_eq_three_of_odd [IsSimpleGroup G]
    (P : Sylow 13 G) (hP : Nat.card P = 13) (hG : Nat.card G ≠ 13)
    (ho : Odd ((centralizer (P : Set G)).relIndex (normalizer (P : Set G)))) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 3 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hd : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ∣ 12 :=
    P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have hn := P.centralizer_relIndex_normalizer_ne_one_of_simple hP hG
  have arith : ∀ m : Fin 13, m.val ∣ 12 → Odd m.val → m.val ≠ 1 → m.val = 3 := by decide
  exact arith ⟨_, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)⟩ hd ho hn

/-- Sylow's congruence, expressed using the normalizer order divided by `p`. -/
public theorem card_div_prime_modEq_of_normalizer_card (P : Sylow p G) {m : ℕ}
    (hN : Nat.card (normalizer (P : Set G)) = p * m) :
    Nat.card G / p ≡ m [MOD p] := by
  have horder : Nat.card G = (Nat.card (Sylow p G) * m) * p := by
    rw [← (normalizer (P : Set G)).index_mul_card,
      ← P.card_eq_index_normalizer, hN]
    ac_rfl
  rw [horder, Nat.mul_div_cancel _ hp.out.pos]
  simpa using (card_sylow_modEq_one p G).mul_right m

end Sylow
