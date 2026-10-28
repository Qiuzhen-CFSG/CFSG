module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Interpretation
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Parity

/-!
# Reduction modulo the actual M₁₁ eleven-norm ideal

Every element of the binary M₁₁ group algebra is congruent modulo the literal
two-sided ideal `elevenIdeal` to a lift of the published 300 coordinates.
Left multiplication by either marked generator agrees with its published
coordinate action modulo that ideal.

`Geometry` identifies the original seeds with actual two-sided translates of
`elevenNorm`; `Parity` proves that their selected sums are the 600 published
column discrepancies. These checked relations extend by linearity, and the
empty basis word and A/B generation give spanning. All finite premises of
`norm_reduction_of_certificates` are discharged here.

Source application: the James reduction used in Aschbacher–Smith G.7.3(2),
printed p.348/PDF p.359. See `NormReduction/source/README.md`.
-/

public section
open scoped MonoidAlgebra
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction
open CertificateData

/-- All 600 literal column discrepancies belong to the actual norm ideal. -/
theorem columnRelations : ColumnRelations :=
  Geometry.columns_of_rowIdentities Parity.rowIdentities

/-- The published coordinate lift spans the actual two-sided norm quotient. -/
theorem exists_lift (x : R) : ∃ v : Space, x - lift v ∈ elevenIdeal :=
  exists_lift_of_columns columnRelations x

/-- The lift intertwines LEFT multiplication by each marked generator modulo
the actual two-sided norm ideal. -/
theorem generator_lift_sub_mem (s : Fin 2) (v : Space) :
    MonoidAlgebra.single (generator s) 1 * lift v - lift (action s v) ∈ elevenIdeal :=
  generator_lift_sub_mem_of_columns columnRelations s v

/-- Unconditional spanning and generator compatibility for the certificate
consumer that transfers the coordinate filtration to the actual norm quotient. -/
theorem norm_reduction :
    (∀ x : R, ∃ v : Space, x - lift v ∈ elevenIdeal) ∧
    (∀ (s : Fin 2) (v : Space),
      MonoidAlgebra.single (generator s) 1 * lift v - lift (action s v) ∈ elevenIdeal) :=
  ⟨exists_lift, generator_lift_sub_mem⟩

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction
