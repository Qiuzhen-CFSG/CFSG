module

public import Stellmacher.SectionEleven.TheoremOneTerminalContext
public import Stellmacher.SectionEleven.TerminalSylowBound

/-!
# The Sylow order addendum to Theorem 1

Under the original Baumann-local hypothesis and the existence of two distinct
maximal two-locals containing the supplied Sylow subgroup, that same Sylow
has order at most 2^15. The native setup constructs an actual terminal context
on a generated pair without changing the supplied Sylow. The complete
terminal bound then applies, retaining both critical distances in the
commuting case and all alternatives in the noncommuting case.

Source: Stellmacher, Journal of Algebra190 (1997), Theorem1 and the opening
case split of Section Eleven. This is the numerical companion to the full
source-local classification, with precisely its original hypotheses.
-/

namespace Stellmacher

universe u

public theorem theorem_one_sylow_card_le
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U →
      baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧
      IsMaximalTwoLocal P1 ∧
      IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧
      (S0 : Subgroup H) ≤ P2) :
    Nat.card S0 ≤ 2 ^ 15 := by
  obtain ⟨P1, P2, ⟨ctx⟩⟩ := SectionEleven.theorem_one_terminal_context S0 hlocal hmax
  exact SectionEleven.sylow_terminal_card_le ctx

end Stellmacher
