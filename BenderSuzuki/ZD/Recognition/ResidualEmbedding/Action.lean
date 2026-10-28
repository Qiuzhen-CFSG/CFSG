module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion

/-!
# Assembly boundary for the residual action theorem

The counting argument of Sections 3--6 produces a distinguished (6A)
configuration if double transitivity fails. The odd-subgroup clause reduces
to the same configuration by prime-order extraction. Finite maximization
then permits the Section 7 contradiction to prove both clauses together.

The counting input is supplied by `actionCounting_of_minimalCounterexample`.
The proved Section 7 maximal-normalizer contradiction excludes every
configuration. Together these supply both clauses of `ResidualAction`,
with no additional source premises.

Source: GLS, Volume 4, Chapter 2, Theorem 4 and Sections 5--7.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory

universe u

/-- Conditional assembly from the counting argument and the Section 7
contradiction. The caller must prove both premises from the genuine ZD
minimal-counterexample hypotheses. -/
public theorem residualAction_of_counting_and_exclusion
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (hc : ActionCounting Z M)
    (exclude : ∀ _d : ActionMaximalCounterexample Z M, False) :
    ResidualAction Z M := by
  have hno : ∀ d : ActionCounterexample Z M, False := by
    intro d
    obtain ⟨e, _, _⟩ := exists_actionMaximalCounterexample d
    exact exclude e
  refine ⟨?_, ?_⟩
  · by_contra hnot
    obtain ⟨z, hzZ, hzM, p, hp, hpOdd, hshare⟩ := hc.prime_share
    obtain ⟨d, _, _, _⟩ := hc.saturated z hzZ hzM p hp hpOdd hshare hnot
    exact hno d
  · intro z hzZ hzM W hWodd hWM hzNorm
    by_cases hcent : W ≤ Subgroup.centralizer ({z} : Set G)
    · exact Or.inl hcent
    · right
      intro beta hbeta
      by_contra hne
      obtain ⟨d, _, _⟩ := actionCounterexample_of_odd_subgroup
        h hzZ hzM hWodd hWM hzNorm hcent hbeta hne
      exact hno d

/-- The complete distinguished action theorem, with Sections 3--7 discharged. -/
public theorem residualAction_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) :
    ResidualAction Z M := by
  have hc := actionCounting_of_minimalCounterexample h r
  exact residualAction_of_counting_and_exclusion h.disconnected hc
    (actionMaximalCounterexample_false h r hc)

end BenderSuzuki.ZD
