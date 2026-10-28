module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.FourAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts
public import Theory.GroupTheory.CyclicFifteen
public import Theory.GroupTheory.PrimeOrderSylowArithmetic

/-!
# Odd centralizers after the group order is known

The actual four-group action on a transfer complement gives its order as
`p*q*r`, where `p` is three or five and `q,r` belong to `{1,3,5}`.
Divisibility by the supplied group order 175560 leaves only `p` and fifteen.
Groups of those orders are cyclic, so this proves the structural input to
Bender's odd-prime calculation without the pre-order exceptional-case work.

The existing numerical calculation then supplies `BenderPrimeData G d`.
Its alternative `d = 1` would give a Sylow three-normalizer of order twelve:
its automizer divides two and is nontrivial by Burnside transfer and simplicity.
This contradicts Sylow's congruence for the supplied group order. Thus `d = 3`,
proving that every element of order three or five has centralizer order thirty,
along with the commuting and inverting counts used by subsequent class work.

Source: Bender, *Finite groups with large subgroups* (1974), §4, (4.1)–(4.2),
and Janko, J. Algebra 3 (1966), Lemma 3.1. This specialized argument uses
an order already available to the ordinary-character construction.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
open Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem complement_card (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {A : Subgroup G} {x : G}
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card A = p ∨ Nat.card A = 15 := by
  obtain ⟨q, r, hq, hr, ha⟩ := a.card_factor_cases p hp hxC hx
  have hd := A.card_subgroup_dvd_card
  rw [horder, ha] at hd
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> norm_num at hd
  all_goals omega

/-- The given group order discharges the actual odd-centralizer decomposition. -/
public theorem oddPrimeCentralizerStructure_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : OddPrimeCentralizerStructure h := by
  refine ⟨?_⟩
  intro p hp x hxC hx
  obtain ⟨A, a⟩ := h.exists_oddCentralizerComplement p hp x hxC hx
  have hc := complement_card h horder a p hp hxC hx
  have hcyc : IsCyclic A := by
    rcases hc with hc | hc
    · rcases hp with rfl | rfl
      · let : Fact (Nat.Prime 3) := ⟨by decide⟩
        exact isCyclic_of_prime_card hc
      · let : Fact (Nat.Prime 5) := ⟨by decide⟩
        exact isCyclic_of_prime_card hc
    · exact isCyclic_of_card_eq_fifteen hc
  have hzC : zpowers h.z ≤ centralizer ({x} : Set G) := a.sup_eq ▸ le_sup_right
  exact ⟨A, hcyc, hc, hzC.trans a.normalizes, a.disjoint, a.sup_eq⟩

private theorem exists_benderPrimeData_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : ∃ d : ℕ, BenderPrimeData G d := by
  obtain ⟨d, hd⟩ := h.exists_localBenderPrimeData_of_structure
    (oddPrimeCentralizerStructure_of_order h horder)
  exact ⟨d, h.benderPrimeData_of_local hd⟩

private theorem parameter_eq_three (horder : Nat.card G = 175560)
    {d : ℕ} (b : BenderPrimeData G d) : d = 3 := by
  rcases b.d_cases with hd | hd
  · subst d
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [horder]; decide)
    let P : Sylow 3 G := Sylow.ofCard (zpowers x) (by
      rw [Nat.card_zpowers, hx, horder]
      decide +kernel)
    have hP : Nat.card P = 3 := b.sylow_three P
    have hC : centralizer (P : Set G) = centralizer ({x} : Set G) := by
      change centralizer (zpowers x : Set G) = centralizer ({x} : Set G)
      rw [zpowers_eq_closure, centralizer_closure]
    have hidx : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 2 := by
      have hdiv := P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
      have hne := P.centralizer_relIndex_normalizer_ne_one_of_simple hP (by rw [horder]; decide)
      exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hne
    have hN : Nat.card (normalizer (P : Set G)) = 12 := by
      have he := ((centralizer (P : Set G)).subgroupOf (normalizer (P : Set G))).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv] at he
      change (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) *
        Nat.card (centralizer (P : Set G)) = _ at he
      rw [hidx, hC, b.centralizer_three x hx] at he
      norm_num at he
      exact he.symm
    have hm := P.card_div_prime_modEq_of_normalizer_card (m := 4) hN
    rw [horder] at hm
    norm_num [Nat.ModEq] at hm
  · exact hd

/-- The source order forces the parameter three in all eight ambient local counts. -/
public theorem benderPrimeData_of_order (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : BenderPrimeData G 3 := by
  obtain ⟨d, hd⟩ := exists_benderPrimeData_of_order h horder
  exact parameter_eq_three horder hd ▸ hd

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
