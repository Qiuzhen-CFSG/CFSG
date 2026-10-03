module

public import Theory.SpecificGroups.ReeTwo.MaximalParityProfiles
public import Theory.SpecificGroups.ReeTwo.TwistedParityCoordinates
public import Theory.SpecificGroups.ReeTwo.TwistedParityFrattini
public import Theory.SpecificGroups.ReeTwo.TwistedParityPowerCounts

/-!
# The twisted Ree two Frattini model

The coordinate map and its ordered representatives are constructed in
`TwistedParityCoordinates` from the verified root multiplication of
Shinoda (1975), (2.3), pp. 81–82. The kernel identity proved in
`TwistedParityFrattini` and the square/fourth-power fiber counts proved in
`TwistedParityPowerCounts` complete the rank-three Frattini model. Its ordered
basis lifts are `rootOne * root 0`, `root 1`, and `root 2`; these core root
indices are shifted by three from Shinoda's indices.
-/

namespace ReeTwo.SylowModel

/-- Kernel identification and power counts complete the constructed coordinate model. -/
public theorem twistedParityFrattiniModel_of_coordinates
    (hker : twistedParityCoordinates.ker = frattini (maximalCharacter 1 1 0).ker)
    (hcount : ∀ v, (twistedParityCoordinates.powerFiberCard v 2,
      twistedParityCoordinates.powerFiberCard v 4) = twistedParityProfile v) :
    TwistedParityFrattiniModel :=
  ⟨twistedParityCoordinates, twistedParityCoordinates_surjective, hker, hcount⟩

/-- The twisted parity kernel has the specified rank-three Frattini quotient
and square/fourth-power fiber counts. -/
public theorem twistedParityFrattiniModel : TwistedParityFrattiniModel :=
  twistedParityFrattiniModel_of_coordinates twistedParityCoordinates_ker_eq_frattini
    twistedParityCoordinates_powerFiberCard

end ReeTwo.SylowModel
