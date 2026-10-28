module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.DegreeCompleteness.Assembly
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Complete

/-!
# The Hall--Janko absolute small-degree window

Every faithful absolutely irreducible representation of the literal degree-100
Hall--Janko carrier over a finite characteristic-two field, of dimension at most
32, has dimension six or fourteen.

The checked modular certificate constructs nine pairwise inequivalent simple
actions of dimensions 6, 6, 14, 14, 36, 64, 64, 84 and 160. Together with the
trivial action, they saturate the proved bound of ten odd-order conjugacy
classes. Thus the only simple degrees at most 32 over an algebraically closed
field are 1, 6 and 14. The scalar-extension assembly preserves dimension and
faithfulness and uses the separately proved faithful lower bound to exclude
one. All presentation, model-construction and conjugacy-coverage premises are
discharged in `ModularCertificate.Complete`.

The earlier conditional assemblies are re-exported from `Assembly` with their
original statements and names. Neither simplicity nor an offender hypothesis
is needed for the completed degree-window theorem.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16; corrected Hiss--Malle Table 2, characteristic-two J₂ rows.
The tables specify the target; completeness follows from the checked actions
and modular trace-independence theorem.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
universe v

/-- A faithful absolutely irreducible characteristic-two representation of the
literal Hall--Janko carrier of degree at most 32 has degree six or fourteen.
There are no remaining certificate or simplicity hypotheses. -/
theorem degreeWindow : DegreeWindow.{v} :=
  degreeWindow_of_closedSmallDegreeSpectrum ModularCertificate.closedSmallDegreeSpectrum

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
