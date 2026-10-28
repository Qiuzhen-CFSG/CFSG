module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.TwoPerfectRefinement
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections

/-!
# Two noncentral intervals in a two-perfect group

Every chief refinement of a noncentral binary interval in a two-perfect
actor contains a noncentral binary chief factor. Refining two successive
such intervals, concatenating, and extending to a complete series gives
a lower bound of two. All intervals retain their original normal subgroups.

Source application: Aschbacher–Smith 14.7.68, printed pp.1071–1072.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]
theorem exists_two_chief_of_two_noncentral (hp : IsPPerfect 2 H)
    (A B : NormalNode H) (hAB : A ≤ B)
    (hA : IsNoncentralTwo ⊥ A) (hB : IsNoncentralTwo A B) :
    ∃ s : ChiefSeries H, s.head = ⊥ ∧ s.last = ⊤ ∧ 2 ≤ s.noncentralTwoCount := by
  obtain ⟨a,ha0,ha1⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  obtain ⟨b,hb0,hb1⟩ := exists_chiefSeries A B hAB
  have ha : 1 ≤ a.noncentralTwoCount := by
    have hh : IsNoncentralTwo a.head a.last := by rwa [ha0,ha1]
    obtain ⟨i,hi⟩ := a.exists_noncentralTwo_of_isPPerfect hp hh
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i,hi⟩⟩,inferInstance⟩
  have hb : 1 ≤ b.noncentralTwoCount := by
    have hh : IsNoncentralTwo b.head b.last := by rwa [hb0,hb1]
    obtain ⟨i,hi⟩ := b.exists_noncentralTwo_of_isPPerfect hp hh
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i,hi⟩⟩,inferInstance⟩
  let s : ChiefSeries H := a.smash b (ha1.trans hb0.symm)
  have hs0 : s.head = ⊥ := by simpa only [s,RelSeries.head_smash] using ha0
  have hs1 : s.last = B := by simpa only [s,RelSeries.last_smash] using hb1
  obtain ⟨t,ht0,ht1,ht⟩ := BinaryFlag.extend_count bot_le le_top s hs0 hs1
  have hcount : 2 ≤ s.noncentralTwoCount := by
    dsimp only [s]
    rw [ChiefSeries.noncentralTwoCount_smash]
    omega
  exact ⟨t,ht0,ht1,hcount.trans ht⟩
end NoncentralChiefRefinement
