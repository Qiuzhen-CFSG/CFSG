module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.DegreeCompleteness.Assembly

/-!
# From the Hall--Janko modular certificate to the finite-field degree window

The saturation certificate supplies the closed-field spectrum. Extension to
an algebraic closure preserves dimension and faithfulness, and absolute
irreducibility gives simplicity there. The independently proved faithful
lower bound excludes degree one. This applies the exact finite-field contract
without adding an offender or field-of-definition hypothesis.

The two model families and exhaustive carrier coverage remain explicit
construction inputs. This application is separate so the spectrum producer
does not import its consumer's assembly module.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16; the characteristic-two J₂ rows of Hiss--Malle corrected Table 2.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
open Sporadic.LeechRelated.J2.PowerFusionCertificate
universe v

/-- Apply the scalar-extension transport and the exclusion of faithful degree
one to the spectrum obtained from the actual model families and class cover. -/
theorem degreeWindow_of_models (hcover : RepresentativeCoverage)
    (hsmall : SmallModelsExist.{v}) (hlarge : LargeModelsExist.{v}) : DegreeWindow.{v} :=
  degreeWindow_of_closedSmallDegreeSpectrum (closedSpectrum_of_models hcover hsmall hlarge)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
