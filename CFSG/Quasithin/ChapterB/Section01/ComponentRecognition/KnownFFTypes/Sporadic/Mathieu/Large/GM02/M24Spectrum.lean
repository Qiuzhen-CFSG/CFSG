module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Source
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Degree
public import Theory.Representation.Mathieu.M24DegreeSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.CentralCover

/-!
# The M₂₄ binary spectrum from the absolute calculations

Remove the center of the original quasisimple group using faithful binary
irreducibility, then transport its actual action through the given quotient
marking. Schur-field descent supplies the binary degree alternatives on the
same vector space. The final theorem applies this spectrum to the existing
GM02 degree-eleven consumer with its generation and displacement inputs.

The complete absolute spectrum and degree-eleven trace calculation now
supply `m24SmallSpectrum` without additional model premises. The earlier
conditional APIs retain their original hypotheses.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

public section
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open Representation.Mathieu.M24DegreeSpectrum
universe u v

/-- Scalar and cover transport of the two independent native calculations. -/
theorem m24SmallSpectrum_of_absolute_calculations
    (hdegree : AbsoluteSmallSpectrum.{v}) (htrace : DegreeElevenTraceField.{v}) :
    M24SmallSpectrum.{u,v} := by
  intro L _ _ _ V _ _ _ σ hf hi he hd
  obtain ⟨e⟩ := he
  let τ := CentralCover.nativeRepresentation σ hf hi e
  let : τ.IsIrreducible := CentralCover.nativeRepresentation_irreducible σ hf hi e
  exact finrank_cases_of_absolute_calculations τ hdegree htrace
    (CentralCover.nativeRepresentation_faithful σ hf hi e) hd

/-- The actual GM02 consumer, retaining only the named independent calculations. -/
theorem m24DegreeEleven_of_absolute_calculations
    (hg : InvolutionGeneration M24 4)
    (hdegree : AbsoluteSmallSpectrum.{v}) (htrace : DegreeElevenTraceField.{v})
    (hmoved : M24Degree44Displacement.{u,v}) : M24DegreeEleven.{u,v} :=
  m24DegreeEleven_of_gm02_inputs hg
    (m24SmallSpectrum_of_absolute_calculations hdegree htrace) hmoved

/-- The native spectrum and trace calculations discharge the complete
cover-preserving binary spectrum contract. -/
theorem m24SmallSpectrum : M24SmallSpectrum.{u,v} :=
  m24SmallSpectrum_of_absolute_calculations absoluteSmallSpectrum degreeElevenTraceField

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
