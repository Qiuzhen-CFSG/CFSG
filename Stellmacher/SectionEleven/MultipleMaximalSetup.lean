module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# The Sylow intersection in the multiple-maximal branch

If two distinct maximal 2-local subgroups contain the fixed Sylow subgroup,
every triple supplied by (5.1) uses that whole Sylow subgroup as its common
2-subgroup. Alternatives (a) and (b) state this equality explicitly, whereas
alternative (c) would make both maximal subgroups equal to its unique maximum.

This is the setup reduction needed before applying the terminal local-type
classification in the multiple-maximal branch of Theorem 2. It uses only the
conditions of (5.1), not a proof of the numbered theorem or the still-unproved
terminal classifications. The stronger Baumann-local hypothesis required by
Sections 8--10 is not asserted here.

Source: `refs/latex/stellmacher-n-group.tex`, alternatives (5.1)(a)--(c) and
the split between multiple and unique maxima at the start of Section 11.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

/-- Distinct maximal 2-locals over `S0` exclude alternative (5.1)(c). -/
public theorem fiveOne_sylow_eq_of_multiple_maximal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 M1 M2 : Subgroup H}
    (hfive : FiveOneConditions H S0 S P1 P2)
    (hne : M1 ≠ M2)
    (hM1 : IsMaximalTwoLocalContaining (S0 : Subgroup H) M1)
    (hM2 : IsMaximalTwoLocalContaining (S0 : Subgroup H) M2) :
    S = (S0 : Subgroup H) := by
  cases hfive.alternative with
  | a hS _ _ => exact hS
  | b hS _ => exact hS
  | c M hM _ _ _ _ _ _ _ _ _ _ =>
    exact False.elim (hne ((hM.2 M1 hM1).trans (hM.2 M2 hM2).symm))

end Stellmacher.SectionEleven
