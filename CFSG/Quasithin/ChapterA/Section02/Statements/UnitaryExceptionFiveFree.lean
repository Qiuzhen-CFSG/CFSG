module
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.SU3.OddBinaryFiveFree
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The unitary exception in Theorem A has order prime to five

Both actual SU₃ factors have odd binary exponents and hence order prime
to five. The product order formula, using their component normalization,
passes this to their generated group and then its literal center quotient.
This rules out the exception for sections involving M₂₂ in the involution
pumpup of 4.2.13; the consumer is ChapterI.Section03.MathieuPumpup.

Source: Aschbacher--Smith A.2.1(1b), printed p.33, and 4.2.13, p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterA.Section02
universe u v
/-- The actual exceptional semisimple section has order prime to five. -/
theorem TheoremAException.five_free {G : Type u} {S : Type v} [Group G] [Finite G]
    [Group S] [Finite S] {p : ℕ} (h : TheoremAException G S p) : ¬ 5 ∣ Nat.card S := by
  obtain ⟨_,H,_,⟨e⟩,⟨d⟩⟩ := h
  have hfactor {B : Type u} [Group B] [Finite B] {n : ℕ}
      (hn : Odd n) (hm : IsSpecialUnitaryModel B 3 (2^n)) : ¬ 5 ∣ Nat.card B := by
    obtain ⟨F,hF,hfin,J,hc,hj,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv]
    exact J.special_card_five_free_of_odd_binary hn hc hj
  have hH : ¬ 5 ∣ Nat.card H := by
    intro hdiv
    have hn : d.second ≤ normalizer (d.first : Set H) := by
      by_cases he : d.first = d.second
      · rw [he]; exact d.second.le_normalizer
      · exact (commutator_eq_bot_iff_le_centralizer.mp
          (d.second_component.commutator_eq_bot_of_ne d.first_component
            (Ne.symm he))).trans (Subgroup.centralizer_le_normalizer _)
    have heq := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.first d.second hn
    rw [d.generates,card_top] at heq
    have hd : 5 ∣ Nat.card d.first * Nat.card d.second := by
      rw [heq]
      exact dvd_mul_of_dvd_right hdiv _
    exact ((by decide : Nat.Prime 5).dvd_mul.mp hd).elim
      (hfactor d.first_odd d.first_model) (hfactor d.second_odd d.second_model)
  rw [Nat.card_congr e.toEquiv]
  exact fun hd => hH (hd.trans (card_quotient_dvd_card (center H)))
end CFSG.Quasithin.ChapterA.Section02

