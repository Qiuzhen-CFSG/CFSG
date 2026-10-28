module

public import BenderSuzuki.External.Huppert.XI.SubgroupInvolutionCore
public import BenderSuzuki.External.Huppert.XI.SubgroupRecognitionData
public import BenderSuzuki.External.Huppert.XI.theorem_11_15

/-!
# Recognition of nonsolvable Suzuki subgroups

Every nonsolvable subgroup of a Suzuki group is itself a Suzuki group.
Its involution fixed points form a nonempty, faithful, doubly transitive
action. The inherited fixed-point bound, absence of regular normal subgroups,
and noncommutative Frobenius 2-kernels give the hypotheses of XI.11.15.

Source: Huppert--Blackburn, *Finite Groups III*, XI.11.15, applied to the
canonical involution action in the subgroup argument of XI.3.12(e).
-/

namespace BenderSuzuki.External

open BenderSuzuki.MatrixGroups

/-- Every nonsolvable subgroup of a Suzuki group is isomorphic to a Suzuki
group with positive parameter. -/
public theorem suzukiSubgroup_exists_mulEquiv_of_not_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H) :
    ∃ k : ℕ, 0 < k ∧ Nonempty (H ≃* SuzukiMatrixGroup k) := by
  let X := suzukiInvolutionSubaction H
  obtain ⟨t, ht⟩ := suzukiSubgroup_exists_involution hm H hH
  let : Nonempty X := suzukiInvolutionSubaction_nonempty hm H t ht
  let := Fintype.ofFinite X
  let := suzukiSubaction_faithful_of_not_isSolvable hm H hH X
  have htwo := suzukiInvolutionSubaction_two_pretransitive hm H hH
  let a : X := Classical.choice inferInstance
  obtain ⟨b, hab, F, hFrob, hFnoncomm, hF2⟩ :=
    suzukiSubaction_noncommutativeFrobeniusTwoKernel_exists hm H hH X htwo a
  exact huppert_XI_11_15_suzukiRecognition htwo
    (suzukiSubaction_at_most_two_fixed hm H X)
    (suzukiSubaction_no_regular_normal hm H hH X htwo)
    a b hab F hFrob hFnoncomm hF2

end BenderSuzuki.External
