module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.LocalAction
public import Theory.GroupAction.KleinFourFactorization

/-!
# The actual four-group action and its fixed subgroups

An involution t in C_G(z) inverting x normalizes the odd complement A, since
N_G(⟨x⟩) normalizes A. Conjugation by z and t gives commuting involutive
automorphisms. Their common fixed subgroup is trivial: C_G(z,t) has order
eight, whereas A has odd order.

The Brauer–Wielandt formula therefore gives
|A| = p |C_A(t)| |C_A(zt)|. Three-fixed-subgroup factorization also expresses
every element of A as a product from ⟨x⟩, C_A(t), C_A(zt). Involution fusion
and the actual A₅ centralizer model restrict the last two orders to 1, 3, 5.
No commutativity or Sylow hypothesis on A is used.

This reconstructs local restrictions for Bender, *Finite groups with large
subgroups* (1974), proof of (4.1), printed p.225, citing Janko (1966),
proof of Lemma 3.1. Further ambient arguments are required to select the
cyclic or elementary-order-27 alternatives.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
  {x : G} {A : Subgroup G}

/-- Inverting the marked generator normalizes the actual odd complement. -/
public theorem OddCentralizerComplement.inverter_mem_normalizer
    (a : OddCentralizerComplement h x A) (t : G) (hti : t * x * t⁻¹ = x⁻¹) :
    t ∈ normalizer (A : Set G) := by
  apply a.normalizer_zpowers_le
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (t * x * t⁻¹) = zpowers x
  rw [hti, zpowers_inv]

omit [Finite G] in
private theorem action_fixed (B : Subgroup G) (t : G) (ht : t ∈ normalizer (B : Set G)) :
    (B.normalizerMonoidHom ⟨t, ht⟩).fixedSubgroup =
      (centralizer ({t} : Set G)).subgroupOf B := by
  ext y
  rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff,
    Subtype.ext_iff]
  change t * (y : G) * t⁻¹ = y ↔ (y : G) * t = t * y
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

omit [Finite G] in
private theorem action_fixed_card (B : Subgroup G) (t : G)
    (ht : t ∈ normalizer (B : Set G)) :
    Nat.card (B.normalizerMonoidHom ⟨t, ht⟩).fixedSubgroup =
      Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  rw [action_fixed, ← card_map_of_injective (f := B.subtype) Subtype.val_injective,
    subgroupOf_map_subtype, inf_comm]

omit [Finite G] in
private theorem action_involutive (B : Subgroup G) (t : G)
    (ht : t ∈ normalizer (B : Set G)) (ht2 : t ^ 2 = 1) :
    Function.Involutive (B.normalizerMonoidHom ⟨t, ht⟩) := by
  have he : (B.normalizerMonoidHom ⟨t, ht⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨t, ht⟩ : normalizer (B : Set G)) ^ 2 = 1
      from Subtype.ext ht2, map_one]
  exact fun y => congrArg (fun f : MulAut B => f y) he

/-- The two involutions act as a four-group with trivial common fixed subgroup. -/
private theorem common_fixed_eq_bot (a : OddCentralizerComplement h x A)
    (t : G) (htC : t ∈ centralizer ({h.z} : Set G)) (ht2 : t ^ 2 = 1)
    (htz : t ∉ zpowers h.z) (htN : t ∈ normalizer (A : Set G)) :
    (A.normalizerMonoidHom ⟨h.z, a.z_mem_normalizer⟩).fixedSubgroup ⊓
      (A.normalizerMonoidHom ⟨t, htN⟩).fixedSubgroup = ⊥ := by
  have hd : Disjoint A (centralizer ({h.z} : Set G) ⊓ centralizer ({t} : Set G)) := by
    apply disjoint_of_coprime_natCard
    rw [h.common_centralizer_card t htC ht2 htz]
    exact a.odd_card.coprime_two_right.pow_right 3
  rw [action_fixed, action_fixed]
  apply bot_unique
  intro y hy
  exact Subtype.ext (show (y : G) = 1 from
    hd.le_bot ⟨y.property, hy.1, hy.2⟩)

/-- The actual fixed subgroups give the order of the complement. -/
public theorem OddCentralizerComplement.four_fixed_card
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (t : G) (htC : t ∈ centralizer ({h.z} : Set G))
    (ht : orderOf t = 2) (htz : t ∉ zpowers h.z) (hti : t * x * t⁻¹ = x⁻¹) :
    Nat.card A = p * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) *
      Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G) := by
  let zN : normalizer (A : Set G) := ⟨h.z, a.z_mem_normalizer⟩
  let tN : normalizer (A : Set G) := ⟨t, a.inverter_mem_normalizer t hti⟩
  have hcomm : Commute zN tN := Subtype.ext (mem_centralizer_singleton_iff.mp htC).symm
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hf := Theory.GroupAction.brauerWielandt_fixedSubgroup_card a.odd_card
    (A.normalizerMonoidHom zN) (A.normalizerMonoidHom tN)
    (action_involutive A h.z a.z_mem_normalizer (h.involution ▸ pow_orderOf_eq_one h.z))
    (action_involutive A t tN.property ht2) (hcomm.map A.normalizerMonoidHom)
  rw [common_fixed_eq_bot a t htC ht2 htz tN.property, card_bot, one_pow, mul_one,
    ← map_mul, action_fixed_card, action_fixed_card, action_fixed_card,
    a.inf_centralizer_eq_zpowers h p hp hxC hx, Nat.card_zpowers, hx] at hf
  exact hf

/-- Three actual involution centralizers factor every element of the complement. -/
public theorem OddCentralizerComplement.four_fixed_factorization
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (t : G) (htC : t ∈ centralizer ({h.z} : Set G))
    (ht : orderOf t = 2) (hti : t * x * t⁻¹ = x⁻¹)
    (y : G) (hy : y ∈ A) :
    ∃ u v w : G, u ∈ zpowers x ∧ v ∈ A ⊓ centralizer ({t} : Set G) ∧
      w ∈ A ⊓ centralizer ({h.z * t} : Set G) ∧ y = u * v * w := by
  let zN : normalizer (A : Set G) := ⟨h.z, a.z_mem_normalizer⟩
  let tN : normalizer (A : Set G) := ⟨t, a.inverter_mem_normalizer t hti⟩
  have hcomm : Commute zN tN := Subtype.ext (mem_centralizer_singleton_iff.mp htC).symm
  obtain ⟨u, v, w, hu, hv, hw, heq⟩ :=
    MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card a.odd_card
      (A.normalizerMonoidHom zN) (A.normalizerMonoidHom tN)
      (action_involutive A h.z a.z_mem_normalizer (h.involution ▸ pow_orderOf_eq_one h.z))
      (action_involutive A t tN.property (ht ▸ pow_orderOf_eq_one t))
      (hcomm.map A.normalizerMonoidHom) ⟨y, hy⟩
  have hu' : u ∈ (centralizer ({h.z} : Set G)).subgroupOf A := by
    rw [← action_fixed A h.z zN.property, MulAut.mem_fixedSubgroup]
    exact hu
  have hv' : v ∈ (centralizer ({t} : Set G)).subgroupOf A := by
    rw [← action_fixed A t tN.property, MulAut.mem_fixedSubgroup]
    exact hv
  have hw' : w ∈ (centralizer ({h.z * t} : Set G)).subgroupOf A := by
    rw [← action_fixed A (h.z * t) (zN * tN).property, MulAut.mem_fixedSubgroup]
    change A.normalizerMonoidHom (zN * tN) w = w
    rw [map_mul]
    exact hw
  refine ⟨u, v, w, ?_, ⟨v.property, hv'⟩, ⟨w.property, hw'⟩, congrArg Subtype.val heq⟩
  rw [← a.inf_centralizer_eq_zpowers h p hp hxC hx]
  exact ⟨u.property, hu'⟩


private theorem product_involution (t : G) (htC : t ∈ centralizer ({h.z} : Set G))
    (ht : orderOf t = 2) (htz : t ∉ zpowers h.z) : orderOf (h.z * t) = 2 := by
  have hc : Commute h.z t := (mem_centralizer_singleton_iff.mp htC).symm
  apply orderOf_eq_prime_iff.mpr
  constructor
  · rw [hc.mul_pow, show h.z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one h.z,
      show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, mul_one]
  · intro he
    apply htz
    have he' : t = h.z⁻¹ := by
      simpa using congrArg (h.z⁻¹ * ·) he
    rw [he']
    exact (zpowers h.z).inv_mem (mem_zpowers h.z)

/-- Each remaining fixed subgroup has order one, three or five. -/
public theorem OddCentralizerComplement.four_fixed_orders [IsSimpleGroup G]
    (a : OddCentralizerComplement h x A) (t : G)
    (htC : t ∈ centralizer ({h.z} : Set G)) (ht : orderOf t = 2)
    (htz : t ∉ zpowers h.z) :
    (Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = 1 ∨
      Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = 3 ∨
      Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = 5) ∧
    (Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G) = 1 ∨
      Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G) = 3 ∨
      Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G) = 5) := by
  have hodd (s : G) : Odd (Nat.card (A ⊓ centralizer ({s} : Set G) : Subgroup G)) :=
    a.odd_card.of_dvd_nat (card_dvd_of_le inf_le_left)
  exact ⟨h.odd_subgroup_centralizing_involution_card _ (hodd t) t ht inf_le_right,
    h.odd_subgroup_centralizing_involution_card _ (hodd (h.z * t)) (h.z * t)
      (product_involution t htC ht htz) inf_le_right⟩

/-- The odd complement order has only six possibilities before further fusion arguments. -/
public theorem OddCentralizerComplement.card_factor_cases [IsSimpleGroup G]
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ∃ q r : ℕ, (q = 1 ∨ q = 3 ∨ q = 5) ∧ (r = 1 ∨ r = 3 ∨ r = 5) ∧
      Nat.card A = p * q * r := by
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  obtain ⟨hq, hr⟩ := a.four_fixed_orders t htC ht htz
  exact ⟨_, _, hq, hr, a.four_fixed_card p hp hxC hx t htC ht htz hti⟩

/-- A bound obtained from the ambient centralizers, without assuming any Sylow status. -/
public theorem OddCentralizerComplement.card_le_twenty_five_mul [IsSimpleGroup G]
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card A ≤ 25 * p := by
  obtain ⟨q, r, hq, hr, he⟩ := a.card_factor_cases p hp hxC hx
  rw [he]
  have hq5 : q ≤ 5 := by rcases hq with rfl | rfl | rfl <;> decide
  have hr5 : r ≤ 5 := by rcases hr with rfl | rfl | rfl <;> decide
  calc
    p * q * r ≤ p * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left p hq5) hr5
    _ = 25 * p := by ring

end CFSG.Quasithin.Janko1CentralizerData
