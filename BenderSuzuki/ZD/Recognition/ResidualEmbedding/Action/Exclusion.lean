module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.FirstStage.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer

/-!
# Final assembly boundary for the distinguished Section 7 exclusion

Corollary 6.4 excludes the concrete Sylow subgroup produced by the source's
maximal-normalizer argument. Generation, Corollary 6.4 and the theta chain
yield Proposition 7.2 from the source hypotheses. The local quotient and
ZJ argument now construct the final maximal-normalizer configuration, so
`actionMaximalCounterexample_false` discharges the Section 7 contradiction.

Source: GLS, Volume 4, Chapter 2, final paragraph of Proposition 7.1.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The concrete final configuration contradicts the ZJ clause of
Corollary 6.4. -/
public theorem actionCounterexample_false_of_final_configuration
    (d : ActionCounterexample Z M) (h64 : ActionCorollary64 d)
    (hfinal : ActionFinalConfiguration d) : False := by
  obtain ⟨beta, hb, hne, htheta, R, hRsyl, hzR⟩ := hfinal
  have hzTheta : d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p (theorem4bSection7D M beta) : Set G) := by
    rw [htheta, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hcontains := action_sylow_contains_oddCore d.hp hRsyl
  obtain ⟨S, hS⟩ := hRsyl
  have hRp : IsPGroup d.p R := by
    rw [hS]
    exact S.isPGroup'.map _
  have hRD : R ≤ theorem4bSection7D M beta := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  exact ((h64 beta hb hne hzTheta).2 R hRp hRD hcontains).1 hzR

/-- GLS Proposition 7.1: no maximal distinguished (6A) configuration exists. -/
public theorem actionMaximalCounterexample_false
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M) : False := by
  have h64 := actionCorollary64_of_minimalCounterexample h r hc d
  have h72 := action_proposition72_of_minimalCounterexample h r hc d
  exact actionCounterexample_false_of_final_configuration d.data h64
    (actionFinalConfiguration_of_firstStage h r hc d h64 h72)

end BenderSuzuki.ZD
