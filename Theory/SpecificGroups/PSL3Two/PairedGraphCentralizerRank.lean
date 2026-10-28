module
public import Theory.GroupTheory.PairedInvolutiveExtension.FixedPairs
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Two.PairedOuterInputs

/-!
# Cubic rank of the actual paired outer-involution centralizer

Each actual outer involution fixes a group of order six. The two fixed groups
embed independently in its paired centralizer, giving three-rank at least two.
This supplies the rank distinction from the source z₂ centralizer in
Aschbacher--Smith 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

public section

namespace Matrix.PSL3Two.PairedGraphCentralizerRank
open Subgroup Theory.GroupTheory.PairedInvolutiveExtension
/-- Both actual graph-fixed S₃ factors contribute a nontrivial cubic rank. -/
theorem two_le_threeRank (α:MulAut SL) (hα:Function.Involutive α)
    (hout : ∀g:SL,α≠MulAut.conj g) :
    2 ≤ primeRank 3 (centralizer ({graph α hα}:Set (Model α hα))) := by
  have hn : primeRank 3 α.fixedSubgroup≠0 := by
    intro hz
    have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    exact hnd (by rw [PairedOuterInputs.card_fixed_of_outer α hα hout]; decide)
  have h := primeRank_graph_centralizer_ge α hα 3
  omega
end Matrix.PSL3Two.PairedGraphCentralizerRank
