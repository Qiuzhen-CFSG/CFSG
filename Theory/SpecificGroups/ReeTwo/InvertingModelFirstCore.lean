module

public import Theory.SpecificGroups.ReeTwo.InvertingModelReduction
public import Theory.SpecificGroups.ReeTwo.InvertingModelSplitZero
public import Theory.SpecificGroups.ReeTwo.InvertingModelNonsplitZero
public import Theory.SpecificGroups.ReeTwo.InvertingModelSix

/-!
# The fixed mark in every inverting census model

For every census action and either fourth power of the cyclic actor, the
embedded last root belongs to the centralizer of the second upper central
term, and every automorphism of that subgroup fixes it.

Marked ambient isomorphisms reduce the forty models to actions 0 and 6 with
the same fourth-power choice. The split action-0 certificate comes from the
root-twisted model. The nonsplit action-0 certificate distinguishes the mark
by its number of fourth roots. For action 6, square-root centralizer orders
distinguish the mark for both choices. All finite certificates are checked
by the kernel in the imported modules.

Source: the verified Shinoda (1975), (2.3), core coordinates and the marked
model reduction in `InvertingModelReduction`. This module is independent of
`InvertingExtensionFirstCore`, which owns transport to arbitrary extensions.
-/

namespace ReeTwo.InvertingModel

/-- Every automorphism of the intrinsic first core fixes the embedded last
root, for all twenty census actions and both actor fourth powers. -/
public theorem centralInvolution_fixed (i : Fin 20) (ε : Bool)
    (a : MulAut (firstCore i ε)) :
    a (centralInvolution i ε) = centralInvolution i ε := by
  apply fixed_of_base_certificates ?_ six_fixed i ε (mark_mem_firstCore i ε) a
  intro η
  cases η with
  | false => exact zero_false_fixed
  | true => exact zero_true_fixed

/-- The fixed-point certificate allows any proof of membership of the mark
in the centralizer of the second upper central term. Membership itself is
provided by `mark_mem_firstCore`. -/
public theorem mark_fixed (i : Fin 20) (ε : Bool)
    (hz : mark i ε ∈ firstCore i ε) (a : MulAut (firstCore i ε)) :
    a ⟨mark i ε, hz⟩ = ⟨mark i ε, hz⟩ :=
  fixed_all_membership_proofs (centralInvolution_fixed i ε) hz a

end ReeTwo.InvertingModel
