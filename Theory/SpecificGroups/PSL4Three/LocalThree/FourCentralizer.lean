module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Theory.SpecificGroups.PSL4Three.LocalThree.Trace
public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer.Lifts
public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer.Commuting
public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer.Anticommuting

/-!
# Four-group centralizers in PSL₄(3)

Choose distinct nonidentity elements of the elementary four-group and lift
them to SL₄(3). The lifts commute or anticommute, retaining the possible
nontrivial scalar commutator. In the commuting case, the trace identities
for both lifts and their product give four joint character lines over F₉.
In the anticommuting case, a change of basis and faithful restriction embed
an auxiliary common centralizer into GL₂(3). These calculations exclude
nine from the ordinary lift centralizer. Central-quotient counting then
excludes nine from the full projective four-group centralizer.

This is a local ingredient for the PSL₄(3) quasithin converse, not an
independent assertion of the classification or of its induction premises.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.LocalThree

/-- The full centralizer of every elementary four-group in the actual
SL₄(3)/Z(SL₄(3)) model has order indivisible by nine. -/
public theorem four_centralizer_not_nine_dvd (A : Subgroup P)
    (hEA : IsElementaryAbelian 2 A) (hA : Nat.card A = 4) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer (A : Set P)) :=
  FourCentralizer.four_centralizer_not_nine_dvd_of_lift_bounds
    FourCentralizer.commuting_lift_centralizer_not_nine_dvd
    FourCentralizer.anticommuting_lift_centralizer_not_nine_dvd A hEA hA

end Matrix.PSL4Three.LocalThree
