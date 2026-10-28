module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels

/-!
# The larger-field parabolic inspection in 15.3.43

The characteristic-two maximality of the actual local image in `I/C_I(L)`
first identifies its component intersection as a maximal proper
S-invariant parabolic. The residual inspection then leaves precisely
PSL₂ and central-quotient PSL₃ in even field degree, or PSU₃, and proves
that intersection is the chosen Borel.

`largerFieldBorel` discharges the recognition premise and lifts the Borel
equality through the component map to `M ∩ L = N_L(S ∩ L)`. The lift retains
the permitted nontrivial central two-covers of PSL₃(4); the inspection
excludes the G₂(4) covers and all other larger-field rank-two models.
No parabolic, Borel equality or surviving family is assumed. The subsequent
Borel-action contradiction is a separate part of 15.3.43.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140; 1.1.5(3)(a)--(c), printed pp.501--502;
and A.2.3--4, printed p.33.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The larger-field classification and literal upstairs Borel equality in
the characteristic-two paragraph of 15.3.43. Both intermediate recognition
and residual-inspection premises are discharged from the reduced configuration. -/
theorem largerFieldBorel (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) {n : ℕ} (hn : 1 < n)
    (hm : Model L z n) : LargerFieldBorel S M L n := by
  obtain ⟨hmodel, hB⟩ := residual_inspection c hz hn hm (quotientParabolic c hz hn hm)
  exact largerFieldBorel_of_quotient c hmodel hB

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
