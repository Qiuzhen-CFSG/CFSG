module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.Blocks
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.FixedOrder
public import Theory.GroupTheory.PrimeOrderCensus
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# The five large-prime classes of the arbitrary J₁ source group

The supplied group order and the already proved centralizers of elements of
orders two, three and five show that a large-prime centralizer divides 1463.
For Sylow subgroups of orders seven, eleven and nineteen, Burnside transfer
makes the automizer nontrivial. Its divisibility by `p - 1` and Sylow's
congruence leave just the numerical cases checked below. The seven case is
self-centralizing; an order-seven element then excludes the spurious
centralizer order 1463 in the other two cases.

The resulting normalizer orders are 42, 110 and 114. The nineteen-normalizer
therefore gives 27720 elements of order nineteen, each in a class of size 9240.
Choosing representatives of these three actual classes, and Cauchy witnesses
for seven and eleven, constructs the literal `LargePrimeBlocks` contract.
No class exhaustion, power-map labeling, or character or model input is used.

Source: Janko, *A new finite simple group with abelian Sylow 2-subgroups and
its characterization*, J. Algebra 3 (1966), 147–186,
DOI 10.1016/0021-8693(66)90010-X; Gorenstein, *Finite Groups*, §16.6,
printed p.482. See `../../Source.md` for the arbitrary-group source context.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
open Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
private theorem not_dvd_centralizer {p q : ℕ} [Fact q.Prime] (x : G)
    (hx : orderOf x = p)
    (hq : ∀ y : G, orderOf y = q → ¬ p ∣ Nat.card (centralizer ({y} : Set G))) :
    ¬ q ∣ Nat.card (centralizer ({x} : Set G)) := by
  intro hd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hd
  have hyG : orderOf (y : G) = q := by simpa using hy
  have hxC : x ∈ centralizer ({(y : G)} : Set G) := by
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp y.property).symm
  have hdiv := (centralizer ({(y : G)} : Set G)).orderOf_dvd_natCard hxC
  rw [hx] at hdiv
  exact hq y hyG hdiv

private theorem centralizer_dvd (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (x : G) (hx : orderOf x = p) :
    Nat.card (centralizer ({x} : Set G)) ∣ 1463 := by
  have b := benderPrimeData_of_order h horder
  have h2 : ¬ 2 ∣ Nat.card (centralizer ({x} : Set G)) := by
    apply not_dvd_centralizer x hx
    intro y hy
    rw [h.involution_centralizer_card y hy]
    rcases hp with rfl | rfl | rfl <;> decide
  have h3 : ¬ 3 ∣ Nat.card (centralizer ({x} : Set G)) := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    apply not_dvd_centralizer x hx
    intro y hy
    rw [b.centralizer_three y hy]
    rcases hp with rfl | rfl | rfl <;> decide
  have h5 : ¬ 5 ∣ Nat.card (centralizer ({x} : Set G)) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply not_dvd_centralizer x hx
    intro y hy
    rw [b.centralizer_five y hy]
    rcases hp with rfl | rfl | rfl <;> decide
  have hc : Nat.Coprime (Nat.card (centralizer ({x} : Set G))) 120 := by
    have c2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
    have c3 := ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3).symm
    have c5 := ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
    exact (c2.pow_right 3).mul_right (c3.mul_right c5)
  have hd := (centralizer ({x} : Set G)).card_subgroup_dvd_card
  rw [horder] at hd
  exact hc.dvd_of_dvd_mul_left hd

private theorem arithmetic_seven : ∀ c ∈ (1463 : ℕ).divisors,
    ∀ a ∈ (6 : ℕ).divisors, 7 ∣ c → a ≠ 1 →
    (175560 / (a * c)) % 7 = 1 → c = 7 ∧ a = 6 := by decide +kernel

private theorem arithmetic_eleven : ∀ c ∈ (1463 : ℕ).divisors,
    ∀ a ∈ (10 : ℕ).divisors, 11 ∣ c → a ≠ 1 →
    (175560 / (a * c)) % 11 = 1 → (c = 11 ∨ c = 1463) ∧ a = 10 := by decide +kernel

private theorem arithmetic_nineteen : ∀ c ∈ (1463 : ℕ).divisors,
    ∀ a ∈ (18 : ℕ).divisors, 19 ∣ c → a ≠ 1 →
    (175560 / (a * c)) % 19 = 1 → (c = 19 ∨ c = 1463) ∧ a = 6 := by decide +kernel

omit [IsSimpleGroup G] in
private theorem prime_sylow_card (horder : Nat.card G = 175560) {p : ℕ}
    [Fact p.Prime] (hp : p = 7 ∨ p = 11 ∨ p = 19) (P : Sylow p G) :
    Nat.card P = p := by
  apply P.card_eq_prime_of_dvd_of_not_sq_dvd
  · rw [horder]; rcases hp with rfl | rfl | rfl <;> decide
  · rw [horder]; rcases hp with rfl | rfl | rfl <;> decide

private theorem prime_arithmetic_inputs (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 11 ∨ p = 19) (P : Sylow p G) :
    let c := Nat.card (centralizer (P : Set G))
    let a := (centralizer (P : Set G)).relIndex (normalizer (P : Set G))
    c ∈ (1463 : ℕ).divisors ∧ a ∣ p - 1 ∧ p ∣ c ∧ a ≠ 1 ∧
      (175560 / (a * c)) % p = 1 := by
  dsimp only
  have hP := prime_sylow_card horder hp P
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  have hxG : orderOf (x : G) = p := by simpa using hx
  have hC : centralizer (P : Set G) = centralizer ({(x : G)} : Set G) := by
    calc
      _ = centralizer (zpowers (x : G) : Set G) :=
        congrArg (fun H : Subgroup G => centralizer (H : Set G))
          (P.zpowers_eq_of_card_eq hP hxG x.property).symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  have hd : Nat.card (centralizer (P : Set G)) ∣ 1463 := by
    rw [hC]; exact centralizer_dvd h horder hp x hxG
  have hpc : p ∣ Nat.card (centralizer (P : Set G)) := by
    rw [hC]
    simpa only [hxG] using (centralizer ({(x : G)} : Set G)).orderOf_dvd_natCard
      (mem_centralizer_singleton_iff.mpr rfl)
  refine ⟨Nat.mem_divisors.mpr ⟨hd, by decide⟩,
    P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP, hpc,
    P.centralizer_relIndex_normalizer_ne_one_of_simple hP ?_, ?_⟩
  · rw [horder]; rcases hp with rfl | rfl | rfl <;> decide
  · have he := ((centralizer (P : Set G)).subgroupOf (normalizer (P : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv] at he
    change (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) *
      Nat.card (centralizer (P : Set G)) = _ at he
    rw [he]
    have hi : (normalizer (P : Set G)).index = 175560 /
        Nat.card (normalizer (P : Set G)) := by
      rw [← horder, ← (normalizer (P : Set G)).index_mul_card,
        Nat.mul_div_cancel _ (Nat.card_pos (α := normalizer (P : Set G)))]
    rw [← hi, ← P.card_eq_index_normalizer]
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]
      using card_sylow_modEq_one p G

private theorem seven_sylow_data (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (P : Sylow 7 G) :
    Nat.card (centralizer (P : Set G)) = 7 ∧
      (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 6 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hc, ha, hp, hn, hm⟩ := prime_arithmetic_inputs h horder (Or.inl rfl) P
  exact arithmetic_seven _ hc _ (Nat.mem_divisors.mpr ⟨ha, by decide⟩) hp hn hm

omit [IsSimpleGroup G] in
private theorem generator_centralizer (horder : Nat.card G = 175560) {p : ℕ}
    [Fact p.Prime] (hp : p = 7 ∨ p = 11 ∨ p = 19)
    {x : G} (hx : orderOf x = p) (P : Sylow p G) (hxP : x ∈ P) :
    centralizer (P : Set G) = centralizer ({x} : Set G) := by
  calc
    _ = centralizer (zpowers x : Set G) :=
      congrArg (fun H : Subgroup G => centralizer (H : Set G))
        (P.zpowers_eq_of_card_eq (prime_sylow_card horder hp P) hx hxP).symm
    _ = _ := by rw [zpowers_eq_closure, centralizer_closure]

private theorem seven_centralizer_card (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (x : G) (hx : orderOf x = 7) :
    Nat.card (centralizer ({x} : Set G)) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨P, hxP⟩ := Sylow.exists_mem_of_orderOf_eq hx
  rw [← generator_centralizer horder (Or.inl rfl) hx P hxP]
  exact (seven_sylow_data h horder P).1

private theorem sylow_centralizer_ne_1463 (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} [Fact p.Prime]
    (hp : p = 11 ∨ p = 19) (P : Sylow p G) :
    Nat.card (centralizer (P : Set G)) ≠ 1463 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP := prime_sylow_card horder (Or.inr hp) P
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  have hxG : orderOf (x : G) = p := by simpa using hx
  have hc := generator_centralizer horder (Or.inr hp) hxG P x.property
  have hn : ¬ 7 ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
    apply not_dvd_centralizer (x : G) hxG
    intro y hy
    rw [seven_centralizer_card h horder y hy]
    rcases hp with rfl | rfl <;> decide
  intro he
  rw [hc] at he
  exact hn (he ▸ (by decide : 7 ∣ 1463))

private theorem largePrime_sylow_data (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 11 ∨ p = 19) (P : Sylow p G) :
    Nat.card (centralizer (P : Set G)) = p ∧
      (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) =
        if p = 11 then 10 else 6 := by
  rcases hp with rfl | rfl | rfl
  · simpa using seven_sylow_data h horder P
  · obtain ⟨hc, ha, hp, hn, hm⟩ := prime_arithmetic_inputs h horder (Or.inr (Or.inl rfl)) P
    obtain ⟨hc', ha'⟩ := arithmetic_eleven _ hc _
      (Nat.mem_divisors.mpr ⟨ha, by decide⟩) hp hn hm
    exact ⟨hc'.resolve_right (sylow_centralizer_ne_1463 h horder (Or.inl rfl) P), ha'⟩
  · obtain ⟨hc, ha, hp, hn, hm⟩ := prime_arithmetic_inputs h horder (Or.inr (Or.inr rfl)) P
    obtain ⟨hc', ha'⟩ := arithmetic_nineteen _ hc _
      (Nat.mem_divisors.mpr ⟨ha, by decide⟩) hp hn hm
    exact ⟨hc'.resolve_right (sylow_centralizer_ne_1463 h horder (Or.inr rfl) P), ha'⟩

/-- Every element of order seven, eleven or nineteen has a centralizer of that
prime order in the ambient source group. -/
public theorem largePrime_centralizer_card_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (x : G) (hx : orderOf x = p) : Nat.card (centralizer ({x} : Set G)) = p := by
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl | rfl <;> decide⟩
  obtain ⟨P, hxP⟩ := Sylow.exists_mem_of_orderOf_eq hx
  rw [← generator_centralizer horder hp hx P hxP]
  exact (largePrime_sylow_data h horder hp P).1

/-- The large-prime Sylow normalizers have orders 42, 110 and 114, respectively. -/
public theorem largePrime_normalizer_card_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (P : Sylow p G) : Nat.card (normalizer (P : Set G)) =
      (if p = 11 then 10 else 6) * p := by
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl | rfl <;> decide⟩
  have he := ((centralizer (P : Set G)).subgroupOf (normalizer (P : Set G))).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv] at he
  change (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) *
    Nat.card (centralizer (P : Set G)) = _ at he
  obtain ⟨hc, ha⟩ := largePrime_sylow_data h horder hp P
  rw [hc, ha] at he
  exact he.symm

/-- There are exactly three actual conjugacy classes of order nineteen. -/
public theorem nineteen_class_count_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : (ConjClasses.ofOrder G 19).card = 3 := by
  classical
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  let P : Sylow 19 G := Classical.choice inferInstance
  have hN : Nat.card (normalizer (P : Set G)) = 114 := by
    simpa using largePrime_normalizer_card_of_order h horder (Or.inr (Or.inr rfl)) P
  have hnum := (normalizer (P : Set G)).index_mul_card
  rw [← P.card_eq_index_normalizer, hN, horder] at hnum
  have hSyl : Nat.card (Sylow 19 G) = 1540 := by omega
  have htotal : Nat.card {x : G // orderOf x = 19} = 27720 := by
    rw [Sylow.card_orderOf_eq_of_card (prime_sylow_card horder (Or.inr (Or.inr rfl))), hSyl]
  have hsizes : ∀ k ∈ ConjClasses.ofOrder G 19, Nat.card k.carrier = 9240 := by
    intro k hk
    obtain ⟨x, rfl, hx⟩ := (ConjClasses.mem_ofOrder_iff 19 k).mp hk
    have he := ConjClasses.nat_card_carrier_mul_card_centralizer x
    rw [largePrime_centralizer_card_of_order h horder (Or.inr (Or.inr rfl)) x hx,
      horder] at he
    omega
  have hs := ConjClasses.sum_card_ofOrder (G := G) 19
  rw [Finset.sum_congr rfl hsizes, htotal] at hs
  simp only [Finset.sum_const, smul_eq_mul] at hs
  omega

omit [IsSimpleGroup G] in
private theorem classBlock_of_class_count {n c m : ℕ}
    (hc : ∀ x : G, orderOf x = n → Nat.card (centralizer ({x} : Set G)) = c)
    (hm : (ConjClasses.ofOrder G n).card = m) : Nonempty (ClassBlock G n c m) := by
  classical
  let e := ((ConjClasses.ofOrder G n).equivFinOfCardEq hm).symm
  choose r hr ho using fun k : ↥(ConjClasses.ofOrder G n) =>
    (ConjClasses.mem_ofOrder_iff n k.val).mp k.property
  refine ⟨{
    representatives := fun i => r (e i)
    orders := fun i => ho (e i)
    centralizers := fun i => hc (r (e i)) (ho (e i))
    distinct := ?_
  }⟩
  intro i j hij
  apply e.injective
  apply Subtype.ext
  exact (hr (e i)).symm.trans (hij.trans (hr (e j)))

omit [Finite G] [IsSimpleGroup G] in
private def singleton_block {p c : ℕ} (x : G) (hx : orderOf x = p)
    (hc : Nat.card (centralizer ({x} : Set G)) = c) : ClassBlock G p c 1 where
  representatives _ := x
  orders _ := hx
  centralizers _ := hc
  distinct _ _ _ := Subsingleton.elim _ _

/-- Construct the five actual classes required by the ordinary-class assembly.
The supplied involution-fusion hypothesis is retained in this interface;
the involution centralizer theorem already follows from the source local data. -/
public theorem nonempty_largePrimeBlocks_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (_hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    Nonempty (LargePrimeBlocks G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [horder]; decide)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 (by rw [horder]; decide)
  obtain ⟨b⟩ := classBlock_of_class_count
    (largePrime_centralizer_card_of_order h horder (Or.inr (Or.inr rfl)))
    (nineteen_class_count_of_order h horder)
  exact ⟨⟨singleton_block x hx (largePrime_centralizer_card_of_order h horder (Or.inl rfl) x hx),
    singleton_block y hy (largePrime_centralizer_card_of_order h horder (Or.inr (Or.inl rfl)) y hy), b⟩⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
