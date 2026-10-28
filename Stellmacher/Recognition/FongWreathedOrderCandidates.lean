module

public import Stellmacher.Recognition.FongWreathedExceptionalCharacters
public import Stellmacher.Recognition.FongWreathedDegrees
public import Stellmacher.Recognition.FongWreathedSevenCentralizer
public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Theory.Character.IrreducibleDegrees

/-!
# Fong's group-order candidates

The actual exceptional packet and the numerical classification give rational
irreducibles of degrees 27, 21 and 7. Schur's bound and degree divisibility
sandwich the group order between divisors of 6048 and 90720. The degree-seven
character makes a Sylow seven subgroup self-centralizing. Its automizer and
Sylow's congruence then give the three possibilities 6048, 18144 and 90720.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp.74–75. The final two character/block
exclusions are separate from this numerical reduction.
-/

public section
namespace Stellmacher.Recognition
open Theory.Character ModularBlock PrincipalBlockConstruction
open FongWreathedIntrinsic FongWreathedExceptional
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
private theorem degree_dvd {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    {n : ℕ} (hn : χ 1 = (n : ℂ)) : n ∣ Nat.card G := by
  have he : hχ.degree = n := by exact_mod_cast hχ.degree_eq.symm.trans hn
  simpa only [he] using hχ.degree_dvd_card

private theorem at_involution {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hJ : χ ((J P : S) : G) = -1) (u : G) (hu : orderOf u = 2) : χ u = -1 := by
  obtain ⟨a, ha⟩ := isConj_iff.mp (isConj_involution_J S P u hu)
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  rw [← ha, ρ.char_conj] at hJ
  exact hJ

namespace FongWreathedExceptional.Characters
variable {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
  {d : PrincipalCongruenceBlockData G} (c : Characters S P d)

/-- The distinguished positive constituent has degree 27. -/
theorem degree_twenty_seven : c.rational.χ₂ 1 = 27 := by
  rw [c.rational.row₂_values.1, c.conditions.classification.1]
  norm_num

include c in
/-- Select both negative constituents in degree order, allowing their exchange. -/
theorem negative_degrees :
    ∃ χ ψ : ClassFunction G,
      IsIrreducibleCharacter χ ∧ IsIrreducibleCharacter ψ ∧
      χ 1 = 21 ∧ ψ 1 = 7 ∧
      (∀ g, ∃ z : ℤ, ψ g = (z : ℂ)) ∧ ψ ((J P : S) : G) = -1 := by
  rcases c.conditions.classification.2 with ⟨h3, h4⟩ | ⟨h4, h3⟩
  · refine ⟨c.rational.χ₃, c.rational.χ₄, c.rational.irreducible.2.1,
      c.rational.irreducible.2.2, ?_, ?_, c.rational.integer_values.2.2, ?_⟩
    · rw [c.rational.row₃_values.1, h3]; norm_num
    · rw [c.rational.row₄_values.1, h4]; norm_num
    · rw [c.rational.row₄_values.2.1, h4]; norm_num
  · refine ⟨c.rational.χ₄, c.rational.χ₃, c.rational.irreducible.2.2,
      c.rational.irreducible.2.1, ?_, ?_, c.rational.integer_values.2.1, ?_⟩
    · rw [c.rational.row₄_values.1, h4]; norm_num
    · rw [c.rational.row₃_values.1, h3]; norm_num
    · rw [c.rational.row₃_values.2.1, h3]; norm_num

include c in
/-- The actual rational degree-seven character, including its value on every
involution. This discharges the inputs of Schur and the seven-centralizer theorem. -/
theorem degree_seven_character :
    ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 7 ∧
      (∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) ∧
      (∀ u : G, orderOf u = 2 → χ u = -1) := by
  obtain ⟨_, χ, _, hχ, _, h7, hi, hJ⟩ := c.negative_degrees
  refine ⟨χ, hχ, h7, ?_, at_involution hχ hJ⟩
  intro g
  obtain ⟨z, hz⟩ := hi g
  exact ⟨(z : ℚ), by simpa using hz⟩

include c in
/-- The Sylow order and the degrees 27 and 21 give the lower divisibility. -/
theorem order_lower : 6048 ∣ Nat.card G := by
  have hS : Nat.card S = 32 := by simpa using P.card
  obtain ⟨χ, _, hχ, _, hd, _⟩ := c.negative_degrees
  exact fong_order_lower_of_degrees _
    (hS ▸ S.1.card_subgroup_dvd_card)
    (degree_dvd c.rational.irreducible.1 c.degree_twenty_seven)
    (degree_dvd hχ hd)

include c in
/-- Schur's upper divisibility from the actual degree-seven constituent. -/
theorem order_upper : Nat.card G ∣ 90720 := by
  obtain ⟨χ, hχ, hd, hr, _⟩ := c.degree_seven_character
  exact hχ.card_dvd_degree_seven_bound S (by simpa using P.card) hd hr
end FongWreathedExceptional.Characters

namespace FongWreathed

/-- The Sylow-seven reduction with the actual automizer retained. -/
theorem sylow_seven_order_candidates (S : Sylow 2 G) (hS : Nat.card S = 32)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1)
    (hl : 6048 ∣ Nat.card G) :
    ∃ T : Sylow 7 G, Nat.card T = 7 ∧
      Subgroup.centralizer (T : Set G) = (T : Subgroup G) ∧
      ((Nat.card G = 6048 ∧ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Set G)) = 3) ∨
       (Nat.card G = 18144 ∧ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Set G)) = 2) ∨
       (Nat.card G = 90720 ∧ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Set G)) = 3)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hu : Nat.card G ∣ 90720 := hχ.card_dvd_degree_seven_bound S hS hdegree hrat
  let T : Sylow 7 G := Classical.choice inferInstance
  have hT : Nat.card T = 7 := T.card_eq_prime_of_dvd_of_not_sq_dvd
    ((by norm_num : 7 ∣ 6048).trans hl)
    (fun h => (by norm_num : ¬ 7 ^ 2 ∣ 90720) (h.trans hu))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup G)) 7
    (by rw [hT])
  have htG : orderOf (t : G) = 7 := (Subgroup.orderOf_coe t).trans ht
  have hz : Subgroup.zpowers (t : G) = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t.property)
      (by rw [Nat.card_zpowers, htG, hT])
  have hC : Subgroup.centralizer (T : Set G) = (T : Subgroup G) := by
    change Subgroup.centralizer ((T : Subgroup G) : Set G) = (T : Subgroup G)
    rw [← hz]
    exact centralizer_zpowers_eq_of_degree_seven S hS hχ hdegree hrat hinv htG
  let r := (Subgroup.centralizer (T : Set G)).relIndex (Subgroup.normalizer (T : Set G))
  have hrdiv : r ∣ 6 := T.centralizer_relIndex_normalizer_dvd_prime_sub_one hT
  have hrne : r ≠ 1 := T.centralizer_relIndex_normalizer_ne_one_of_simple hT
    (by intro he; rw [he] at hl; norm_num at hl)
  have hr : r = 2 ∨ r = 3 ∨ r = 6 := by
    have hrle := Nat.le_of_dvd (by decide : 0 < 6) hrdiv
    interval_cases r <;> norm_num at *
  have hN := T.normalizer_card_of_self_centralizing hT hC
  have hcong : Nat.card G / (7 * r) % 7 = 1 := by
    have he : Nat.card G / (7 * r) = Nat.card (Sylow 7 G) := by
      rw [T.card_eq_index_normalizer]
      have hm := (Subgroup.normalizer (T : Set G)).index_mul_card
      have hnpos := Nat.card_pos (α := Subgroup.normalizer (T : Set G))
      rw [hN] at hm hnpos
      rw [← hm, Nat.mul_div_cancel _ hnpos]
    rw [he]
    exact card_sylow_modEq_one 7 G
  refine ⟨T, hT, hC, ?_⟩
  have h := fong_order_possibilities (Nat.card G) r hl hu hr hcong
  simpa only [r, hC] using h

/-- The original group hypotheses supply a self-centralizing subgroup of order
seven and the three numerical order alternatives. -/
theorem exists_seven_subgroup_and_order_candidates
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ Z : Subgroup G, Nat.card Z = 7 ∧ Subgroup.centralizer (Z : Set G) = Z ∧
      ((Nat.card G = 6048 ∧ Z.relIndex (Subgroup.normalizer (Z : Set G)) = 3) ∨
       (Nat.card G = 18144 ∧ Z.relIndex (Subgroup.normalizer (Z : Set G)) = 2) ∨
       (Nat.card G = 90720 ∧ Z.relIndex (Subgroup.normalizer (Z : Set G)) = 3)) := by
  obtain ⟨P, d, ⟨c⟩⟩ := exists_characters S hS x hx
  obtain ⟨χ, hχ, hd, hr, hi⟩ := c.degree_seven_character
  obtain ⟨T, hT, hC, ho⟩ := sylow_seven_order_candidates S
    (by simpa using P.card) hχ hd hr hi c.order_lower
  exact ⟨T, hT, hC, ho⟩

end FongWreathed
end Stellmacher.Recognition
