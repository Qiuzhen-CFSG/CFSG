module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Checker

/-!
# Ordinary subgroup recovery from word equations

A checked equation expressing a generator as a word transfers membership using
only multiplication and inversion in the specified subgroup. The interval
lemmas assemble the finite family of recovered symbols without a long case split.
This is the final recovery step for Bray's Held M₁ Schreier presentation.
-/

public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Replay
open Theory.GroupTheory.CosetEnumeration

theorem generator_mem_from_fact {G : Type*} [Group G] {g : Nat → G}
    (H : Subgroup G) {a : Nat} {w : Word Nat}
    (hf : Holds g ([(a, true)], w)) (hw : eval g w ∈ H) : g a ∈ H := by
  have he : g a = eval g w := by
    simpa only [Holds, eval_singleton, letterValue, if_true] using hf
  exact he.symm ▸ hw

theorem range_singleton {P : Nat → Prop} (a : Nat) (h : P a) :
    ∀ n, a ≤ n → n < a + 1 → P n := by
  intro n hn hn'
  have : n = a := by omega
  exact this.symm ▸ h

theorem range_join {P : Nat → Prop} {lo mid hi : Nat}
    (hleft : ∀ n, lo ≤ n → n < mid → P n)
    (hright : ∀ n, mid ≤ n → n < hi → P n) :
    ∀ n, lo ≤ n → n < hi → P n := by
  intro n hn hn'
  by_cases hm : n < mid
  · exact hleft n hn hm
  · exact hright n (Nat.le_of_not_gt hm) hn'

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Replay
