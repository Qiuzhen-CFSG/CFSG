module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.Blocks
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.FixedOrder
public import Theory.GroupTheory.PrimeOrderCensus
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# The classes of orders three and five in the arbitrary J₁ source group

Both prime-order Sylow normalizers have order sixty. Their automizer orders
are nontrivial divisors of two and four, respectively; Sylow's congruence
excludes order four for the five-automizer when the ambient order is 175560.
The disjoint Sylow census therefore gives 5852 elements of order three and
11704 of order five. The fixed-order centralizer theorem gives every such
class size 5852, yielding one and two actual classes, respectively.

The representatives are chosen from these actual ambient conjugacy classes.
No recognition, character data, representation or compatible power labeling
is used. The normalizer orders are also available for the cyclic-fifteen
branch of the local class calculation.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. See `../../Source.md` for the source conventions.
-/

open Subgroup
open scoped BigOperators
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
open Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_centralizer_card {p c : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : Nat.card P = p)
    (hc : ∀ x : G, orderOf x = p → Nat.card (centralizer ({x} : Set G)) = c) :
    Nat.card (centralizer (P : Set G)) = c := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  have hx' : orderOf (x : G) = p := by simpa only [Subgroup.orderOf_coe] using hx
  change Nat.card (centralizer ((P : Subgroup G) : Set G)) = c
  rw [← P.zpowers_eq_of_card_eq hP hx' x.property, zpowers_eq_closure,
    centralizer_closure]
  exact hc x hx'

omit [Finite G] in
private theorem normalizer_card_eq (s : Set G) :
    Nat.card (normalizer s) =
      (centralizer s).relIndex (normalizer s) *
        Nat.card (centralizer s) := by
  have he := ((centralizer s).subgroupOf (normalizer s)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer s)).toEquiv] at he
  exact he.symm

variable [IsSimpleGroup G]

/-- Every Sylow three-subgroup has ambient normalizer order sixty. -/
public theorem sylow_three_normalizer_card (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (P : Sylow 3 G) :
    Nat.card (normalizer (P : Set G)) = 60 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have b := benderPrimeData_of_order h horder
  have hP := b.sylow_three P
  have hC : Nat.card (centralizer (P : Set G)) = 30 :=
    sylow_centralizer_card P hP (by simpa using b.centralizer_three)
  have hd := P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have hn := P.centralizer_relIndex_normalizer_ne_one_of_simple hP (by rw [horder]; decide)
  have hi : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  rw [normalizer_card_eq (P : Set G), hi, hC]

/-- Sylow's congruence excludes an automizer of order four at five. -/
public theorem sylow_five_normalizer_card (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (P : Sylow 5 G) :
    Nat.card (normalizer (P : Set G)) = 60 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have b := benderPrimeData_of_order h horder
  have hP := b.sylow_five P
  have hC : Nat.card (centralizer (P : Set G)) = 30 :=
    sylow_centralizer_card P hP (by simpa using b.centralizer_five)
  have hd := P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have hn := P.centralizer_relIndex_normalizer_ne_one_of_simple hP (by rw [horder]; decide)
  have arith : ∀ i : Fin 5, i.val ∣ 4 → i.val ≠ 1 → i.val = 2 ∨ i.val = 4 := by decide
  have hi : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 2 ∨
      (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 4 :=
    arith ⟨_, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)⟩ hd hn
  rcases hi with hi | hi
  · rw [normalizer_card_eq (P : Set G), hi, hC]
  · have hN : Nat.card (normalizer (P : Set G)) = 120 := by
      rw [normalizer_card_eq (P : Set G), hi, hC]
    have hm := P.card_div_prime_modEq_of_normalizer_card (m := 24) hN
    rw [horder] at hm
    norm_num [Nat.ModEq] at hm

/-- The arbitrary source group has exactly 5852 elements of order three. -/
public theorem card_order_three (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : Nat.card {x : G // orderOf x = 3} = 5852 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := default
  have he := (normalizer (P : Set G)).index_mul_card
  rw [← P.card_eq_index_normalizer, sylow_three_normalizer_card h horder, horder] at he
  rw [Sylow.card_orderOf_eq_of_card (benderPrimeData_of_order h horder).sylow_three]
  omega

/-- The arbitrary source group has exactly 11704 elements of order five. -/
public theorem card_order_five (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : Nat.card {x : G // orderOf x = 5} = 11704 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := default
  have he := (normalizer (P : Set G)).index_mul_card
  rw [← P.card_eq_index_normalizer, sylow_five_normalizer_card h horder, horder] at he
  rw [Sylow.card_orderOf_eq_of_card (benderPrimeData_of_order h horder).sylow_five]
  omega

omit [IsSimpleGroup G] in
private theorem class_count_mul_size (n c : ℕ) (hcpos : 0 < c)
    (hc : ∀ x : G, orderOf x = n → Nat.card (centralizer ({x} : Set G)) = c) :
    (ConjClasses.ofOrder G n).card * (Nat.card G / c) =
      Nat.card {x : G // orderOf x = n} := by
  classical
  have hs (k : ConjClasses G) (hk : k ∈ ConjClasses.ofOrder G n) :
      Nat.card k.carrier = Nat.card G / c := by
    obtain ⟨x, rfl, hx⟩ := (ConjClasses.mem_ofOrder_iff n k).mp hk
    have he := ConjClasses.nat_card_carrier_mul_card_centralizer x
    rw [hc x hx] at he
    rw [← he, Nat.mul_div_cancel _ hcpos]
  rw [← ConjClasses.sum_card_ofOrder]
  simp only [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul]

omit [IsSimpleGroup G] in
private theorem classBlock_of_card (n c k : ℕ)
    (hc : ∀ x : G, orderOf x = n → Nat.card (centralizer ({x} : Set G)) = c)
    (hk : (ConjClasses.ofOrder G n).card = k) : Nonempty (ClassBlock G n c k) := by
  classical
  let e := (Finset.equivFinOfCardEq hk).symm
  have hex (i : Fin k) : ∃ x : G, ConjClasses.mk x = (e i).val ∧ orderOf x = n :=
    (ConjClasses.mem_ofOrder_iff n (e i).val).mp (e i).property
  choose r hr ho using hex
  refine ⟨⟨r, ho, fun i => hc (r i) (ho i), ?_⟩⟩
  intro i j hij
  apply e.injective
  exact Subtype.ext (by simpa only [hr] using hij)

/-- Construct the actual order-three block, with ambient centralizer order thirty. -/
public theorem three_classes_nonempty (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : Nonempty (ClassBlock G 3 30 1) := by
  have hc : ∀ x : G, orderOf x = 3 → Nat.card (centralizer ({x} : Set G)) = 30 :=
    by simpa using (benderPrimeData_of_order h horder).centralizer_three
  apply classBlock_of_card 3 30 1 hc
  have he := class_count_mul_size 3 30 (by decide) hc
  rw [horder, card_order_three h horder] at he
  omega

/-- Construct two nonconjugate order-five representatives, each with ambient centralizer order thirty. -/
public theorem five_classes_nonempty (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : Nonempty (ClassBlock G 5 30 2) := by
  have hc : ∀ x : G, orderOf x = 5 → Nat.card (centralizer ({x} : Set G)) = 30 :=
    by simpa using (benderPrimeData_of_order h horder).centralizer_five
  apply classBlock_of_card 5 30 2 hc
  have he := class_count_mul_size 5 30 (by decide) hc
  rw [horder, card_order_five h horder] at he
  omega

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
