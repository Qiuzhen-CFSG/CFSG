module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OrderSixOvergroups
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterReduction

/-!
# The actual action census from its marked outer quotient

The proved order-six conjugacy theorem discharges the finite-subgroup premise
of the reduction on the actual second Tits core. Construction of the marked
outer quotient remains explicit. Its discharge and the original-source
second-parabolic assembly belong to qt-e-quintic-second-parabolic.
Source: Aschbacher--Smith F.1.12 and14.2.21, pp.263,988--989.
-/

public section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open Subgroup

/-- Conjugacy of the actual action images, conditional only on the marked
outer quotient construction. -/
theorem action_census_of_outer_quotient
    (q : MulAut Core →* OuterModel) (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup Core)
    (v : BinaryPair) (hv : markedTransposition v ∈ sylow.range.map q)
    (A : Subgroup (MulAut Core)) (hA : sylow.range ≤ A)
    (hc : Nat.card (center Core) * Nat.card A = 6144) :
    ∃ α : MulAut Core, A.map (MulAut.congr α).toMonoidHom = model.range :=
  action_census_of_marked_outer_quotient q hq hk v hv
    marked_order_six_conjugacy A hA hc

end Tits.ExceptionalParabolics.SecondCoreAction
