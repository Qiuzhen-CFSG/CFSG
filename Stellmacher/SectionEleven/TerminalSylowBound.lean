module

public import Stellmacher.SectionEleven.CommutingSylowBound
public import Stellmacher.SectionEleven.NoncommutingSylowBound

/-!
# The full terminal Sylow bound

A Sylow terminal context gives the source bound of 2^15 on the order of its
original ambient Sylow subgroup. Split according to whether the critical
center subgroups commute and use the two native bounds. Both retain the
original Sylow through the generated join, and the commuting branch retains
critical distance one as well as three. No all-two-local solvability or named
model recognition hypothesis is required.

This is the numerical terminal assembly for the addendum to Stellmacher's
Theorem 1, via the case split at the start of Section Eleven.
-/

namespace Stellmacher.SectionEleven

universe u

public theorem sylow_terminal_card_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2) :
    Nat.card S0 ≤ 2 ^ 15 := by
  by_cases hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥
  · exact commuting_terminal_sylow_card_le ctx hcomm
  · exact noncommuting_terminal_sylow_card_le ctx hcomm

end Stellmacher.SectionEleven
