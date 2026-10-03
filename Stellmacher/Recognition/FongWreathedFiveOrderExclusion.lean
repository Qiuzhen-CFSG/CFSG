module

public import Stellmacher.Recognition.FongWreathedSevenCentralizer
public import Stellmacher.Recognition.FongWreathedOrderCandidates
public import Stellmacher.Recognition.FongWreathedEvenFiveCentralizer
public import Stellmacher.Recognition.FongWreathedFiveBlockExclusion
public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Theory.Character.ConstantRestriction
public import Theory.Character.DegreeSevenMixedOrder

/-!
# Five-centralizer reductions for Fong's order exclusion

For a rational degree-seven character with value minus one on involutions,
an odd five-centralizer has order dividing 405: self-centralization at seven
excludes the remaining prime. If its nonidentity three-elements have value
four, restriction averaging bounds its Sylow three-subgroup by order three.
Excluding centralizer order five therefore leaves order fifteen. The actual
normalizer action and Sylow congruence then exclude ambient order 90720.

The local even-centralizer exclusion, the cyclic-five-block exclusion of a
centralizer of order five, and the mixed-order trace calculation remain inputs
of the final reduction theorem. They are not assumed as block axioms.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp.74–75.
-/

namespace Stellmacher.Recognition.FongWreathed
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer order fifteen forces a normalizer order incompatible with
Sylow's congruence when the ambient order is 90720. -/
public theorem not_card_90720_of_centralizer_five_card_fifteen
    {s : G} (hs : orderOf s = 5)
    (hC : Nat.card (Subgroup.centralizer ({s} : Set G)) = 15) :
    Nat.card G ≠ 90720 := by
  intro hG
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨T, hle⟩ := (IsPGroup.of_card (show Nat.card (Subgroup.zpowers s) = 5 ^ 1 by
    rw [Nat.card_zpowers, hs, pow_one])).exists_le_sylow
  have hT : Nat.card T = 5 := T.card_eq_prime_of_dvd_of_not_sq_dvd
    (by rw [hG]; norm_num) (by rw [hG]; norm_num)
  have hz : Subgroup.zpowers s = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hs, hT])
  have hCT : Nat.card (Subgroup.centralizer (T : Set G)) = 15 := by
    change Nat.card (Subgroup.centralizer ((T : Subgroup G) : Set G)) = 15
    rw [← hz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hC
  let C := Subgroup.centralizer (T : Set G)
  let N := Subgroup.normalizer (T : Set G)
  let k := C.relIndex N
  have hk : k ∣ 4 := T.centralizer_relIndex_normalizer_dvd_prime_sub_one hT
  have hN : Nat.card N = 15 * k := by
    have h := (C.subgroupOf N).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (T : Set G))).toEquiv, hCT] at h
    exact h.symm
  have hcong : Nat.card G / 5 ≡ 3 * k [MOD 5] :=
    T.card_div_prime_modEq_of_normalizer_card (by dsimp [N] at hN; omega)
  rw [hG] at hcong
  have hkle : k ≤ 4 := Nat.le_of_dvd (by decide) hk
  have hk3 : k = 3 := by
    norm_num [Nat.ModEq] at hcong
    omega
  norm_num [hk3] at hk

/-- An odd five-centralizer has order dividing `5 * 3^4`. -/
public theorem five_centralizer_card_dvd_of_odd [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 32) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1)
    {s : G} (hs : orderOf s = 5)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({s} : Set G))) :
    Nat.card (Subgroup.centralizer ({s} : Set G)) ∣ 405 := by
  let C := Subgroup.centralizer ({s} : Set G)
  have h7 : ¬ 7 ∣ Nat.card C := by
    intro hd
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 7 hd
    have htG : orderOf (t : G) = 7 := (Subgroup.orderOf_coe t).trans ht
    have hCt := centralizer_eq_zpowers_of_degree_seven S hS hχ hdegree hrat hinv htG
    have hsC : s ∈ Subgroup.centralizer ({(t : G)} : Set G) := by
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp t.property).symm
    have hdiv := orderOf_dvd_natCard
      (⟨s, hsC⟩ : Subgroup.centralizer ({(t : G)} : Set G))
    rw [← Subgroup.orderOf_coe, hs, hCt, Nat.card_zpowers, htG] at hdiv
    norm_num at hdiv
  have hcop : (Nat.card C).Coprime (2^5 * 7) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm.pow_right 5).mul_right
      ((show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr h7).symm
  have hd := C.card_subgroup_dvd_card.trans
    (hχ.card_dvd_degree_seven_bound S hS hdegree hrat)
  apply hcop.dvd_of_dvd_mul_left
  norm_num at hd ⊢
  exact hd

/-- Averaging on the actual Sylow three-subgroup gives centralizer order
fifteen once order five is excluded and the three-elements have value four. -/
public theorem five_centralizer_card_eq_fifteen_of_three_values
    {χ : ClassFunction G} (hχ : IsCharacter χ) (hdegree : χ 1 = 7)
    {s : G} (hs : orderOf s = 5)
    (hdiv : Nat.card (Subgroup.centralizer ({s} : Set G)) ∣ 405)
    (hne : Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 5)
    (hvalue : ∀ g : G, g ∈ Subgroup.centralizer ({s} : Set G) → g ≠ 1 →
      (∃ e : ℕ, orderOf g = 3 ^ e) → χ g = 4) :
    Nat.card (Subgroup.centralizer ({s} : Set G)) = 15 := by
  let C := Subgroup.centralizer ({s} : Set G)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let T : Sylow 3 C := Classical.choice inferInstance
  let H : Subgroup G := (T : Subgroup C).map C.subtype
  have hH : Nat.card H = Nat.card T :=
    (Nat.card_congr ((T : Subgroup C).equivMapOfInjective C.subtype
      Subtype.val_injective).toEquiv).symm
  have hv : ∀ g ∈ H, g ≠ 1 → χ g = 4 := by
    intro g hg hgne
    obtain ⟨t, ht, rfl⟩ := hg
    apply hvalue t t.property hgne
    obtain ⟨e, he⟩ := T.isPGroup'.exists_orderOf_eq_pow (⟨t, ht⟩ : T)
    exact ⟨e, (Subgroup.orderOf_coe t).trans
      ((Subgroup.orderOf_coe (⟨t, ht⟩ : (T : Subgroup C))).trans he)⟩
  have hTdiv : Nat.card T ∣ 3 := by
    have hd : (Nat.card H : ℤ) ∣ (3 : ℤ) := by
      simpa using hχ.card_dvd_degree_sub_of_constant H 7 4 hdegree hv
    rw [hH] at hd
    exact Int.natCast_dvd_natCast.mp hd
  have h9 : ¬ 9 ∣ Nat.card C := by
    intro hd
    have := (T.pow_dvd_card_of_pow_dvd_card (show 3^2 ∣ Nat.card C from hd)).trans hTdiv
    norm_num at this
  have h5 : 5 ∣ Nat.card C := by
    have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    simpa only [← Subgroup.orderOf_coe, hs] using
      orderOf_dvd_natCard (⟨s, hsC⟩ : C)
  have arith : ∀ n : Fin 406, n.val ∣ 405 → 5 ∣ n.val → ¬ 9 ∣ n.val →
      n.val = 5 ∨ n.val = 15 := by
    set_option maxRecDepth 2048 in decide
  exact (arith ⟨Nat.card C, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hdiv)⟩
    hdiv h5 h9).resolve_left hne
/-- Assembly of the five-centralizer exclusion from its three remaining
character and local inputs. The full exclusion must discharge these inputs
from the original wreathed and solvable involution-centralizer hypotheses. -/
public theorem not_card_90720_of_five_centralizer_inputs [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 32) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1)
    {s : G} (hs : orderOf s = 5)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)))
    (hne : Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 5)
    (hvalue : ∀ g : G, g ∈ Subgroup.centralizer ({s} : Set G) → g ≠ 1 →
      (∃ e : ℕ, orderOf g = 3 ^ e) → χ g = 4) : Nat.card G ≠ 90720 := by
  have hchar : IsCharacter χ := by
    obtain ⟨n, ρ, _, hρ⟩ := hχ
    exact ⟨n, ρ, hρ⟩
  exact not_card_90720_of_centralizer_five_card_fifteen hs
    (five_centralizer_card_eq_fifteen_of_three_values hchar hdegree hs
      (five_centralizer_card_dvd_of_odd S hS hχ hdegree hrat hinv hs hodd)
      hne hvalue)

/-- The original wreathed and solvable-involution-centralizer hypotheses exclude
order `90720`.  The exceptional packet supplies the degree-seven character;
the even-five local argument, cyclic five-block argument, and mixed-order
trace calculation discharge the three inputs of the conditional reduction. -/
public theorem not_card_90720_of_wreathed
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card G ≠ 90720 := by
  intro hG
  obtain ⟨P, d, hc⟩ := FongWreathedExceptional.exists_characters S hS x hx
  obtain ⟨c⟩ := hc
  obtain ⟨χ, hχ, hdegree, hrat, hinv⟩ := c.degree_seven_character
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hSCard : Nat.card S = 32 := by
    simpa using P.card
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 (by
    rw [hG]
    norm_num)
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
    intro heven
    obtain ⟨y, hy⟩ := exists_order_twenty_of_even_five_centralizer
      S hS x hx hG hs heven P
    exact hχ.degree_seven_orderOf_ne_twenty hdegree hrat hinv y hy
  have hne : Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 5 := by
    exact five_centralizer_card_ne_five c hG hs
  have hvalue : ∀ g : G, g ∈ Subgroup.centralizer ({s} : Set G) → g ≠ 1 →
      (∃ e : ℕ, orderOf g = 3 ^ e) → χ g = 4 := by
    intro g hg hgne hpower
    exact hχ.degree_seven_three_element_value_of_centralizes_five
      hdegree hrat hs hg hgne hpower
  exact (not_card_90720_of_five_centralizer_inputs S hSCard hχ hdegree hrat hinv
    hs hodd hne hvalue) hG

end Stellmacher.Recognition.FongWreathed
