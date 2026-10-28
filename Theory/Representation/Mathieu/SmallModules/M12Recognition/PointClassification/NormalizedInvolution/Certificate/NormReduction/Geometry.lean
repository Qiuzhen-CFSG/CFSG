module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Model
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.BasisLeft
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Interpretation

/-!
# Actual M11 geometry of the norm certificate

The packed action certificate identifies the indexed words with the literal
two-sided eleven-norm translates, published basis words, and LEFT multiplication
by the marked generators. These unconditional geometric facts feed the decoder;
the independent binary row identities remain with their own assembly producer.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

open Sporadic.Mathieu Inputs CertificateData
open scoped MonoidAlgebra

/-- All original seeds are the stated literal two-sided eleven-norm translates. -/
theorem seedGeometry : SeedGeometry := by
  intro k t
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro x
  apply Fin.ext
  change ((indexElement (seedEntry k t)).val x).val =
    ((indexElement (translateLeft k)).val
      ((m11Sylow11Generator ^ t.val).val ((indexElement (translateRight k)).val x))).val
  rw [index_point, index_point, sylow_point, index_point]
  exact seed_point k t x

/-- The indexed basis agrees with the already-published actual words. -/
theorem basisGeometry : BasisGeometry := by
  intro j
  exact congrArg CertificateData.evalWord (basis_words j)

/-- The checked target indices implement LEFT multiplication by A and B. -/
theorem leftGeometry : LeftGeometry := by
  intro s j
  rw [← basisGeometry j]
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro x
  apply Fin.ext
  change ((indexElement (leftIndex s j)).val x).val =
    ((generator s).val ((indexElement (basisIndex j)).val x)).val
  rw [index_point, generator_digit, index_point]
  exact left_points s j x

/-- Consumer: each original seed lies in the literal TWO-SIDED norm ideal. -/
theorem decoded_seed_mem (k : Seed) : decode (seedVector k) ∈ elevenIdeal :=
  decode_seed_mem seedGeometry k

/-- Consumer: the indexed column is the actual left-generator lift discrepancy. -/
theorem decoded_column (s : Fin 2) (j : Fin 300) :
    decode (columnVector s j) =
      MonoidAlgebra.single (generator s) 1 * basisElement j -
        lift (action s (Pi.single j 1)) :=
  decode_column basisGeometry leftGeometry s j

/-- Only the independent cancellation certificate remains for norm reduction. -/
theorem columns_of_rowIdentities (hr : RowIdentities) : ColumnRelations :=
  columns_of_certificates seedGeometry basisGeometry leftGeometry hr

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
