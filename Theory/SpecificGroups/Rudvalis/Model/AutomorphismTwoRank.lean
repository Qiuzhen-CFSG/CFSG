module
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Automorphism two-rank of the Rudvalis carrier

The proved realization of every automorphism as inner and the intrinsic
rank-six calculation give the same bound on the full automorphism group.
Simplicity is inherited from the actual source central quotient. The
six-dimensional point-component comparison uses this bound directly.
Source: GLS3 Table 5.3r and Aschbacher--Smith 10.2.9, pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace Rudvalis
/-- The full automorphism group has two-rank at most six. -/
theorem automorphism_rank_le_six [IsSimpleGroup Model] :
    primeRank 2 (MulAut Model) ≤ 6 := by
  let e : Model ≃* MulAut Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot LowCentralizers.model_center_eq_bot,
      component_conj_surjective⟩
  rw [←primeRank_equiv 2 e]
  exact primeRank_le_six
end Rudvalis
