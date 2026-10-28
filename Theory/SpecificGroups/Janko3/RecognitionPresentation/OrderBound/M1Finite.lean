module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation

/-!
# Reduction of the literal J₃ subgroup bound to local relations and enumeration

The original eight relators already imply `x² = 1` and `z⁴ = 1` for the
advertised subgroup generator `z = (y*x)^5*y⁻¹*x*y*x*y`. Four further word
identities give an epimorphism from the separate local presentation to the
literal subgroup `M1`. A finite bound for that presentation, or a checked
2040-coset cover by its cyclic subgroup, then proves the required bound for M₁.

The four identities and the local cover remain explicit inputs. In particular,
this module does not yet assert unconditional finiteness of M₁.

Source: ATLAS J3G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound

/-- Transfer from the separate six-relator presentation to the literal M₁.
The independent producers must discharge both explicit premises. -/
public theorem m1_finite_card_of_local_relations
    (hrel : M1Finite.RemainingRelations)
    (hlocal : Finite M1Finite.LocalPresentation.Carrier ∧
      Nat.card M1Finite.LocalPresentation.Carrier ≤ 8160) :
    Finite M1 ∧ Nat.card M1 ≤ 8160 :=
  M1Finite.LocalPresentation.closure_finite_card
    (M1Finite.satisfies_of_remaining hrel) hlocal

/-- The actual subgroup application of the 2040-coset local certificate. -/
public theorem m1_finite_card_of_local_cover
    (hrel : M1Finite.RemainingRelations)
    (C : Subgroup.GeneratorCosetCover M1Finite.LocalPresentation.cyclicSubgroup
      M1Finite.LocalPresentation.generator (Fin 2040)) :
    Finite M1 ∧ Nat.card M1 ≤ 8160 :=
  m1_finite_card_of_local_relations hrel (M1Finite.LocalPresentation.finite_card_of_cover C)

end Sporadic.Janko3.RecognitionPresentation.OrderBound
