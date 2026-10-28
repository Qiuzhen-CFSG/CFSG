module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Reduction
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions.Counting

/-!
# The full binary Ree first-restriction lower bound

Three explicitly constructed automorphisms of the genuine first endpoint,
together with inner automorphisms of the Sylow overlap, give at least 16384
distinct restrictions along the specified embedding. The counting proof uses
three proper subgroup enlargements and retains no extra finite-model premise.

Applying this bound to the marked reduction leaves only the independently
produced Sylow-automorphism upper bound and the second-endpoint separator.
The full rigidity assembly remains in the parent module.
Source context: Shinoda (1975), pp.81–83; Parrott (1972), p.683;
Aschbacher–Smith F.1.11–12, printed pp.262–263.
-/

public section
namespace Tits.AmalgamRigidity.FullRee
open Theory.GroupTheory RankTwoAmalgam

/-- Unconditional lower bound on actual compatible first-endpoint restrictions. -/
theorem firstRestrictions_card_ge : 16384 ≤ Nat.card firstRestrictions :=
  FirstRestrictions.restriction_card_ge

/-- The first count is discharged; only the other two finite inputs remain. -/
theorem factorsThrough_of_firstRestrictions_bound
    (haut : Nat.card (MulAut ReeTwo.SylowModel) ≤ 32768)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions)
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_bounds haut firstRestrictions_card_ge hsecond d

end Tits.AmalgamRigidity.FullRee
