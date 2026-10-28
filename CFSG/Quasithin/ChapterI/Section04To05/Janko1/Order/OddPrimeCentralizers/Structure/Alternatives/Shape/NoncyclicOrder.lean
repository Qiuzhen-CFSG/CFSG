module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.AbelianConsequences
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.PrimeCube
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.PrimeSupport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.QuinticActor

/-!
# Noncyclic abelian odd complements have order twenty-seven

Normalizer fusion in `PrimeCube` restricts a noncyclic complement to
orders 27 or 125. In the latter case, `QuinticActor` constructs an element
u of order three fixing both an involution and a nonidentity element of A.

If a complement A has order 125, its exponent divides five. An element
u of order three that centralizes an involution therefore cannot fix a
nonidentity element of A: its odd complement B would contain a five-element.
Prime support then identifies |B| with |A|, contradicting 3 dividing |B|.
This excludes 125 and completes the order restriction.

Universal commutativity of the source complements remains explicit, to be
discharged by the parent shape assembly. No complement order, Sylow status
or exceptional normalizer configuration is assumed. Source: Bender (1974),
proof of (4.1), printed p.225 (PDF p.3), citing Janko (1966), proof of
Lemma 3.1, DOI 10.1016/0021-8693(66)90010-X.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}

/-- Under the order-125 hypothesis, a three-element centralizing an involution
has no nontrivial fixed point on the actual complement. -/
public theorem OddCentralizerComplement.inf_three_centralizer_eq_bot_of_card_125
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hcard : Nat.card A = 125)
    (u t : G) (hu : orderOf u = 3) (ht : orderOf t = 2) (hut : Commute u t) :
    A ⊓ centralizer ({u} : Set G) = ⊥ := by
  have ha := allComm h p hp x hxC hx A a
  have hp5 : p = 5 := by
    have hd := Subgroup.orderOf_dvd_natCard A a.x_mem
    rw [hx, hcard] at hd
    rcases hp with hp | hp
    · rw [hp] at hd
      norm_num at hd
    · exact hp
  have hx5 : orderOf x = 5 := hx.trans hp5
  obtain ⟨k, hk⟩ := h.exists_data_at_involution t ht
  have huC : u ∈ centralizer ({k.z} : Set G) := by
    rw [hk, mem_centralizer_singleton_iff]
    exact hut.eq
  obtain ⟨B, b⟩ := k.exists_oddCentralizerComplement 3 (Or.inl rfl) u huC hu
  have hb := allComm k 3 (Or.inl rfl) u huC hu B b
  apply bot_unique
  rintro y ⟨hyA, hyu⟩
  change y = 1
  by_contra hy1
  have hy15 : orderOf y ∣ 15 := by
    apply orderOf_dvd_of_pow_eq_one
    exact congrArg Subtype.val
      (a.pow_fifteen_of_commutative 5 (Or.inr rfl) hxC hx5 ha ⟨y, hyA⟩)
  have hy125 : orderOf y ∣ 125 := hcard ▸ Subgroup.orderOf_dvd_natCard A hyA
  have hy5 : orderOf y = 5 := by
    have hd : orderOf y ∣ 5 := by simpa using Nat.dvd_gcd hy15 hy125
    exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left
      (fun he => hy1 (orderOf_eq_one_iff.mp he))
  have hyB : y ∈ B := (b.mem_iff_odd_orderOf hyu).mpr (a.odd_orderOf hyA)
  have hd5 : 5 ∣ Nat.card B := hy5 ▸ Subgroup.orderOf_dvd_natCard B hyB
  have hBA := b.card_eq_of_prime_dvd a hb allComm 3 (Or.inl rfl) huC hu
    5 (Or.inr rfl) hxC hx5 hd5
  have hd3 := Subgroup.orderOf_dvd_natCard B b.x_mem
  rw [hu, hBA, hcard] at hd3
  norm_num at hd3

/-- An actual three-element fixing an involution and a nontrivial point
excludes order 125; its construction is a separate ambient obligation. -/
public theorem OddCentralizerComplement.card_ne_125_of_fixed_three
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (u t y : G) (hu : orderOf u = 3) (ht : orderOf t = 2)
    (hut : Commute u t) (hyA : y ∈ A) (hy : y ≠ 1) (huy : Commute u y) :
    Nat.card A ≠ 125 := by
  intro hcard
  have he := a.inf_three_centralizer_eq_bot_of_card_125 allComm p hp hxC hx hcard
    u t hu ht hut
  exact hy (show y ∈ (⊥ : Subgroup G) from
    he ▸ (show y ∈ A ⊓ centralizer ({u} : Set G) from
      ⟨hyA, mem_centralizer_singleton_iff.mpr huy.symm.eq⟩))

/-- The constructed cubic actor excludes order 125, with no additional
fixed-point or normalizer premise. -/
public theorem OddCentralizerComplement.card_ne_125
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card A ≠ 125 := by
  intro hcard
  obtain ⟨u, t, y, hu, ht, hut, hyA, hy, huy⟩ :=
    a.exists_fixed_three_of_card_125 (allComm h p hp x hxC hx A a) p hp hxC hx hcard
  exact a.card_ne_125_of_fixed_three allComm p hp hxC hx u t y hu ht hut hyA hy huy hcard

/-- A noncyclic odd complement has order twenty-seven under exactly the
universal commutativity premise retained by the parent shape assembly. -/
public theorem OddCentralizerComplement.card_eq_twenty_seven_of_noncyclic
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hncyc : ¬ IsCyclic A) : Nat.card A = 27 := by
  exact Or.resolve_right
    (a.card_eq_twenty_seven_or_one_twenty_five_of_noncyclic allComm p hp hxC hx hncyc)
    (a.card_ne_125 allComm p hp hxC hx)

end CFSG.Quasithin.Janko1CentralizerData
