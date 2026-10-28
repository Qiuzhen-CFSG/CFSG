module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Coordinates
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.OrbitBalance

/-!
# Independent inputs for the binary Ree torus spectrum

`Placement` requires an actual conjugator into the literal positive coroot
product. `Balance` requires equality of the fixed short- and long-root character
counts for any such presentation of an order-five or order-thirteen Ree element.
`PrimeSpectrumBound` is the finite character calculation for a nonidentity tuple
of fifth or thirteenth roots of unity with those equal counts.

These are separate proof obligations, not assertions that the source theorem
has been proved. The coverage assembly transports the element order through the
actual embedding to obtain the coordinate power equations, applies the finite
bound, and converts it to twenty moving end-node characters.

Source: Guralnick--Malle II, Lemma 8.8 (internal p.57), and GLS3, Sections 1.14
and 2.8. Final discharge of all three obligations belongs to `TorusCoverage`.
-/

public section

open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage

@[expose] def Placement (F : Type*) [Field F] [IsAlgClosed F] : Prop :=
  ∀ (f : CoefficientField 0 →+* F) (x : Model 0),
    (orderOf x = 5 ∨ orderOf x = 13) →
    ∃ (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ),
      Classification.splitEmbedding f (toSplitGroup 0 x) =
        c * corootTorusElement t * c⁻¹

@[expose] def Balance (F : Type*) [Field F] [IsAlgClosed F] : Prop :=
  ∀ (f : CoefficientField 0 →+* F) (x : Model 0),
    (orderOf x = 5 ∨ orderOf x = 13) →
    ∀ (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ),
      Classification.splitEmbedding f (toSplitGroup 0 x) =
        c * corootTorusElement t * c⁻¹ → ShortLongBalance t

@[expose] def PrimeSpectrumBound (F : Type*) [Field F] : Prop :=
  ∀ (p : ℕ), (p = 5 ∨ p = 13) → ∀ t : Fin 4 → Fˣ,
    t ≠ 1 → (∀ i, t i ^ p = 1) → ShortLongBalance t →
      fixedWeightCount EndNode.endOrbitWeight t ≤ 4

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
