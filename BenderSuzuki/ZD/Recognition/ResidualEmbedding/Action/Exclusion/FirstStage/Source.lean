module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.FirstStage
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting

/-!
# The first stage of distinguished Section 7 from its source hypotheses

The proved theta chain and Corollary 6.4 give a nonbase pair with trivial
theta core (Proposition 7.2). If double transitivity failed, the counting
argument would supply a maximal (6A) witness with inverted cardinality
m_p. Proposition 7.9 makes that cardinality strictly smaller than m_p,
a contradiction. This proves the double-transitivity clause of Theorem 4.

The second stage, excluding all (6A) witnesses using maximal normalizers,
is still needed for the odd-subgroup clause of the full action theorem.
Source: GLS, Volume 4, Chapter 2, Propositions 7.2, 7.8 and 7.9.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Proposition 7.2 with generation and the theta comparison discharged. -/
public theorem action_proposition72_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M) :
    Theorem4bProposition72 d.data.toTheorem4bSixA :=
  action_proposition72_of_theta_chain d.data
    (actionCorollary64_of_minimalCounterexample h r hc d)
    (actionThetaChain_of_minimalCounterexample h r hc d)

/-- The double-transitivity clause of the distinguished action theorem. -/
public theorem action_two_transitive_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) :
    MulAction.IsMultiplyPretransitive G (G ⧸ M) 2 := by
  by_contra hnot
  have hc := actionCounting_of_minimalCounterexample h r
  obtain ⟨z, hzZ, hzM, p, hp, hpOdd, hshare⟩ := hc.prime_share
  obtain ⟨d, _, _, _⟩ := hc.saturated z hzZ hzM p hp hpOdd hshare hnot
  obtain ⟨e, _, _⟩ := exists_actionMaximalCounterexample d
  exact hnot (e.two_transitive_of_proposition72 h.disconnected hc
    (actionCorollary64_of_minimalCounterexample h r hc e)
    (action_proposition72_of_minimalCounterexample h r hc e))

end BenderSuzuki.ZD
