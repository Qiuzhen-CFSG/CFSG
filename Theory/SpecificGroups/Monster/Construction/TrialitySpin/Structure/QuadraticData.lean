module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CocodeActions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.BasicSubgroups

/-!
# Coordinates for the source quadratic quotient

Exercise 4.6 uses `V × V*` as a set with a twisted addition, not the ordinary
product vector space. We use the actual Golay cocode for `V*`, via its proved
perfect pairing. The definitions below transcribe that addition, the quadratic
function, and its proposed polar form. The vector-space laws, quadratic laws,
and identification with the group quotient are separate theorem obligations.

For the source word `ψ₁(d) ψ₂(π^t) ψ₁(α_c)`, the coordinate is
`(d.code + t • golayOne, c)`. The word `q1Word` already reverses its factors for
Lean's composition convention; this does not change the source coordinates.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.6, printed p. 64, specialized
to the Parker loop in Lemmas 27.1–27.2, printed pp. 144–145.
-/

@[expose] public section
noncomputable section

open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin

/-- The underlying set of the quadratic quotient; no product addition is used. -/
@[ext] structure QuadraticCoordinates where
  code : golay
  cocode : Cocode

/-- The zero coordinates in Exercise 4.6. -/
def coordinateZero : QuadraticCoordinates := ⟨0, 0⟩

/-- The exact twisted sum from Exercise 4.6. -/
def coordinateSum (x y : QuadraticCoordinates) : QuadraticCoordinates :=
  ⟨x.code + y.code + golayHalfOverlap x.code y.code • golayOne,
    x.cocode + y.cocode + intersectionCocode x.code y.code⟩

/-- The square function in the source coordinates. -/
def coordinateQuadratic (x : QuadraticCoordinates) : ParkerBit :=
  (1 + cocodeParity x.cocode) * golayQuarterWeight x.code +
    cocodePairing x.code x.cocode

/-- The commutator form in the source coordinates. -/
def coordinatePolar (x y : QuadraticCoordinates) : ParkerBit :=
  cocodePairing y.code x.cocode + cocodePairing x.code y.cocode +
    cocodeParity x.cocode * golayQuarterWeight y.code +
    cocodeParity y.cocode * golayQuarterWeight x.code + golayHalfOverlap x.code y.code

/-- The source coordinate assigned to a specialized normal-form word. -/
def q1WordCoordinates (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    QuadraticCoordinates := ⟨d.1 + t • golayOne, c⟩

end Sporadic.Monster.Construction.TrialitySpin
