module

public import Theory.SpecificGroups.ReeTwo.ParityFrattiniCoordinates
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniKernel
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniPowerCounts

/-!
# The Ree two parity Frattini model

The explicit rank-four map and its surjectivity are established in
`ParityFrattiniCoordinates`. The kernel identity in `ParityFrattiniKernel`
and the square and fourth-power counts in `ParityFrattiniPowerCounts` complete
the model predicate used by the automorphism argument. The resulting quotient
has the ordered basis lifted by rootOne², root 0, root 1, and root 2.

The coordinates and ordered basis follow Shinoda (1975), (2.3), pp. 81–82;
see `ParityFrattiniCoordinates` for the link to the verified root action.
-/

namespace ReeTwo.SylowModel

/-- Assemble the explicit quotient after proving its Frattini identity and power counts. -/
public theorem parityFrattiniModel_of_coordinates
    (hker : parityProjection.ker = frattini ParityKernel)
    (hcounts : ∀ v, (parityProjection.powerFiberCard v 2,
      parityProjection.powerFiberCard v 4) = parityProfile v) : ParityFrattiniModel :=
  ⟨parityProjection, parityProjection_surjective, hker, hcounts⟩

/-- The parity kernel has the specified rank-four Frattini quotient and power counts. -/
public theorem parityFrattiniModel : ParityFrattiniModel :=
  parityFrattiniModel_of_coordinates parityProjection_ker_eq_frattini
    parityProjection_powerFiberCounts

end ReeTwo.SylowModel
