module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Application
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact

/-!
# The checked characteristic-two Hall--Janko degree certificate

The exact five-relator presentation descends the nine checked matrix actions
to the literal degree-100 permutation carrier. Their dimensions are
6, 6, 14, 14, 36, 64, 64, 84 and 160. The model constructions prove
irreducibility over every algebraically closed characteristic-two field and
distinguish equal-degree pairs by traces of the same carrier words.

The proved representative coverage bounds the number of odd-order conjugacy
classes by ten. Adding the trivial action therefore saturates the modular
simple-count bound. Every simple action of dimension at most 32 has dimension
1, 6 or 14. Scalar extension to an algebraic closure and the faithful degree
lower bound give the exact finite-field `DegreeWindow` contract.

All construction, presentation and coverage premises are discharged here.
No character table, offender hypothesis or alternate carrier is assumed.
Sources: the ATLAS J2 matrix candidates and J2G1-P2; the low-degree statement
used in Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16. See `Source.md` for attribution and certificate conventions.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
open Sporadic.LeechRelated.J2
universe v

/-- Four actual pairwise inequivalent simple actions in degrees 6, 6, 14 and 14,
with the marked presentation exactness discharged. -/
theorem smallModelsExist : SmallModelsExist.{v} :=
  smallModelsExist_of_presentation_injective
    G2FourModule.Embedding.InnerRealization.PresentationExact.toCarrier_injective

/-- Five actual pairwise inequivalent simple actions in degrees
36, 64, 64, 84 and 160, with no remaining construction premises. -/
theorem largeModelsExist : LargeModelsExist.{v} :=
  LargeModels.modelsExist
    G2FourModule.Embedding.InnerRealization.PresentationExact.toCarrier_injective

/-- The literal carrier has at most ten characteristic-two regular classes. -/
theorem pRegular_class_bound_le_ten :
    Nat.card (ConjClasses.mk '' {g : Carrier | ¬2 ∣ orderOf g}) ≤ 10 :=
  odd_class_bound PowerFusionCertificate.representativeCoverage

/-- Over every algebraically closed characteristic-two field, the only simple
degrees at most 32 are 1, 6 and 14. -/
theorem closedSmallDegreeSpectrum : ClosedSmallDegreeSpectrum.{v} :=
  closedSpectrum_of_models PowerFusionCertificate.representativeCoverage
    smallModelsExist largeModelsExist

/-- Every faithful absolutely irreducible action of the literal carrier over
a finite characteristic-two field, of degree at most 32, has degree 6 or 14. -/
theorem degreeWindow : DegreeWindow.{v} :=
  degreeWindow_of_closedSmallDegreeSpectrum closedSmallDegreeSpectrum

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
