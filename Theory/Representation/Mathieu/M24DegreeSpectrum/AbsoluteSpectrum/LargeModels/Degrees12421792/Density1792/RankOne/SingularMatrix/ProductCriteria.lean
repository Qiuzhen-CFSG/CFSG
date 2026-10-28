module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# Packed multiplication by the actual ATLAS generators

These applications of the carry-free checker use the literal, untransposed
`Data1792` arrays. They are numerical certificate interfaces for computing
words in the two parts of the singular expression. The expanded-row checks
and product checks are explicit obligations, never inferred from external data.
See `source/README.md` for the two expression producers and final assembly.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open Thompson.BinaryMatrix

/-- A checked right multiplication by the literal first ATLAS generator. -/
theorem mul_first_of_checks (a w c : List Nat) (ha : a.length = 1792)
    (hw : Wide.checkSpreadRows 1792 Data1792.firstRows.toList w = true)
    (h : Wide.checkRows 1792 a w c = true) :
    decode 1792 a.toArray * Data1792.first = decode 1792 c.toArray := by
  exact Wide.product_sound 1792 a Data1792.firstRows.toList w c (by decide) ha
    (by decide +kernel) hw h

/-- A checked right multiplication by the literal second ATLAS generator. -/
theorem mul_second_of_checks (a w c : List Nat) (ha : a.length = 1792)
    (hw : Wide.checkSpreadRows 1792 Data1792.secondRows.toList w = true)
    (h : Wide.checkRows 1792 a w c = true) :
    decode 1792 a.toArray * Data1792.second = decode 1792 c.toArray := by
  exact Wide.product_sound 1792 a Data1792.secondRows.toList w c (by decide) ha
    (by decide +kernel) hw h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
