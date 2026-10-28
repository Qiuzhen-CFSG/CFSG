module

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Noncentral binary chief factors bound the group order

Every automorphism of a group of order two fixes its unique nonidentity
point. Thus a noncentral binary section has order at least four. Multiplying
the orders of the literal relative quotients telescopes along a chief series;
each counted section contributes a factor of at least four, while all other
sections contribute at least one. A complete series therefore satisfies
`4 ^ noncentralTwoCount ≤ Nat.card K`.

This argument needs no solvability or classification hypothesis. Its source
application is the five-factor obstruction in Aschbacher–Smith 14.7.70,
printed p.1074, assembled in Goldschmidt/TripleCore/SourceAssembly.lean.
-/

public section

open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K] [Finite K]

/-- A noncentral binary section cannot have order one or two. -/
theorem IsNoncentralTwo.four_le_card (A B : NormalNode K) (h : IsNoncentralTwo A B) :
    4 ≤ Nat.card (Section A B) := by
  obtain ⟨n, hn⟩ := h.1.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hnlt : n < 2 := by omega
    interval_cases n
    · have hone : Nat.card (Section A B) = 1 := by simpa using hn
      let : Subsingleton (Section A B) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact h.2 ((isCentral_iff_action A B).mpr (fun _ _ => Subsingleton.elim _ _))
    · have htwo : Nat.card (Section A B) = 2 := by simpa using hn
      obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : Section A B)).mp htwo
      apply h.2
      apply (isCentral_iff_action A B).mpr
      intro k x
      by_cases hx : x = 1
      · simp [hx]
      · exact (hz _ (fun he => hx ((sectionAction A B k).injective
          (he.trans (map_one _).symm)))).trans (hz x hx).symm
  rw [hn]
  exact (show (2 : ℕ) ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn2)

omit [Finite K] in
/-- The relative quotient counts the index of the lower endpoint. -/
theorem section_card_mul (A B : NormalNode K) (hAB : A ≤ B) :
    Nat.card (Section A B) * Nat.card A.val = Nat.card B.val := by
  have hc := Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv
  rw [← hc]
  exact (A.val.subgroupOf B.val).index_mul_card

/-- Multiplication of the actual section orders telescopes along the series. -/
theorem ChiefSeries.prod_card_section_mul_head (s : ChiefSeries K) :
    (∏ i : Fin s.length, Nat.card (Section (s i.castSucc) (s i.succ))) *
      Nat.card s.head.val = Nat.card s.last.val := by
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < ∏ i : Fin s.length, Nat.card (s i.castSucc).val from
      Finset.prod_pos (fun _ _ => Nat.card_pos))
  calc
    _ = Nat.card s.head.val *
        (∏ i : Fin s.length, Nat.card (Section (s i.castSucc) (s i.succ)) *
          Nat.card (s i.castSucc).val) := by rw [Finset.prod_mul_distrib]; ac_rfl
    _ = Nat.card s.head.val * ∏ i : Fin s.length, Nat.card (s i.succ).val := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact section_card_mul _ _ (s.isChief i).lt.le
    _ = ∏ i : Fin (s.length + 1), Nat.card (s i).val := (Fin.prod_univ_succ (fun i => Nat.card (s i).val)).symm
    _ = _ := by rw [Fin.prod_univ_castSucc]; exact Nat.mul_comm _ _

open Classical in
omit [Finite K] in
private theorem count_pow_eq_product (s : ChiefSeries K) :
    4 ^ s.noncentralTwoCount =
      ∏ i : Fin s.length, if IsNoncentralTwo (s i.castSucc) (s i.succ) then 4 else 1 := by
  classical
  simp [ChiefSeries.noncentralTwoCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.prod_ite]

/-- Each counted factor contributes at least four to the endpoint ratio. -/
theorem ChiefSeries.four_pow_noncentralTwoCount_mul_head_le_last (s : ChiefSeries K) :
    4 ^ s.noncentralTwoCount * Nat.card s.head.val ≤ Nat.card s.last.val := by
  classical
  rw [← s.prod_card_section_mul_head]
  apply Nat.mul_le_mul_right
  rw [count_pow_eq_product]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro i _
  split_ifs with h
  · exact IsNoncentralTwo.four_le_card _ _ h
  · exact Nat.card_pos

/-- A complete chief series bounds the ambient order by its noncentral count. -/
theorem ChiefSeries.four_pow_noncentralTwoCount_le_card (s : ChiefSeries K)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    4 ^ s.noncentralTwoCount ≤ Nat.card K := by
  have h := s.four_pow_noncentralTwoCount_mul_head_le_last
  rw [h0, h1] at h
  change 4 ^ s.noncentralTwoCount * Nat.card (⊥ : Subgroup K) ≤
    Nat.card (⊤ : Subgroup K) at h
  simpa only [card_bot, card_top, Nat.mul_one] using h

end NoncentralChiefRefinement
