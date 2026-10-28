module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Data
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate

/-!
# The distinguished maximal-normalizer argument

Proposition 7.2 selects a nonbase pair with trivial theta. The first stage
supplies the maximal-normalizer data; the actual local quotient and ZJ
factorization give an admissible conjugate of Ω₁(Z(J(R))). Maximality and
the p-group normalizer condition then make the conjugate of R Sylow in D.

The only explicit source premises are Corollary 6.4 and Proposition 7.2,
which the Section 7 exclusion assembly supplies.
Source: GLS, Volume 4, Chapter 2, Proposition 7.9 through the end of
Proposition 7.1.
-/

namespace BenderSuzuki.ZD
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The concrete final Sylow configuration from the first stage of Section 7. -/
public theorem actionFinalConfiguration_of_firstStage
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA) :
    ActionFinalConfiguration d.data := by
  obtain ⟨beta, hb, hne, htheta⟩ := h72
  obtain ⟨q⟩ := actionMaximalNormalizerData_of_firstStage h r hc d h64
    ⟨beta, hb, hne, htheta⟩ hb hne htheta
  exact actionFinalConfiguration_of_admissible_conjugate d.data hb hne htheta q
    (action_exists_admissible_ZJ_conjugate h r d.data hne q)

end BenderSuzuki.ZD
