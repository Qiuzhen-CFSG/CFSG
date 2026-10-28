module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BinaryOuter
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.LinearThreeRestriction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelInner.Linear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelInner.Unitary
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# Parameter restrictions and inner action in the rank-one branch of 15.3.37

`RankOneAction.Setup` records the genuine preceding local conclusions.
The component's two-core and the initial model list are independent inputs.
The Sylow restrictions give even linear and unitary exponents, exclude
opposite-sign PSL₃ models larger than PSL₃(2), and restrict the
Fermat--Mersenne primes to 5 and 7 through actual exceptional isomorphisms.
For both Lie-rank-one families the invariant Borel is M ∩ L and normalizes
Y₊; its concrete torus action forces innerness. For PSL₃(2), the proved
coverage by standard automorphisms makes the actual outer quotient a
two-group, so the two-perfect group Y₊ has trivial outer image.

`Setup.rankOneModel_and_inner` assembles these branches with no remaining
parameter, Borel or automorphism premise. Its inner-action witnesses lie in
the genuine section kernel on L/O₂(L). The initial model and two-core
reduction are independent inputs; the subsequent product and three-part
conclusions belong to the parent assembly using 15.3.12.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.37, printed p.1135, with the local setup on pp.1123--1125 and 1134.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G} (h : Setup Yplus S M I L)
include h

/-- All initial rank-one possibilities satisfy the source parameter restrictions. -/
theorem Setup.rankOneModel (hm : RankOneInitialModel L) : RankOneModel L := by
  rcases h.rankOneModel_or_linear_three hm with hm | ⟨n, hn, hmod, hm⟩
  · exact hm
  · have he := h.linear_three_exponent_eq_one (by omega : 0 < n) hmod hm
    omega

/-- The binary rank-three model has inner Y₊-action, using full standard
automorphism coverage and the actual outer quotient. -/
theorem Setup.psl3_two_inner (hm : ClassicalGroup.IsPSL L 3 2) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  apply h.inner_of_psl3_two_coverage hm
  exact Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card
    (ZMod 2) (m := 1) (by decide) (by simp)

/-- The model and inner-action conclusions of the rank-one paragraph of
15.3.37. The odd-core input is 15.3.11(8); the initial-model reduction
supplies the component model and its trivial two-core independently. -/
theorem Setup.rankOneModel_and_inner
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    (hm : RankOneInitialModel L) :
    RankOneModel L ∧ ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  have hmodel := h.rankOneModel hm
  refine ⟨hmodel, ?_⟩
  rcases hmodel with ⟨n, hn, heven, hm⟩ | ⟨n, hn, heven, hm⟩ | hm
  · exact h.linear_inner hodd hcore hn heven hm
  · exact h.unitary_inner hodd hcore hn heven hm
  · exact h.psl3_two_inner hm

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
