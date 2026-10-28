module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Transport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Complete

/-!
# Radical-form certificate for the literal Mathieu seed

The exports certify independence and dimension 1221 of the original exterior
family, and identify its raw radical space with the span of the exact ten
saved radical forms. The ten forms are independent; the full adapted pullbacks
and Wall-adjoint equations are certified finite identities.

`Complete` discharges the coefficient-completeness premise of `Transport`.
It constructs `radicalBasis` with the exact prescribed underlying matrices
and proves `finrank_radicalForms = 10`, taking only the explicit kernel-range
hypothesis. Establishing that geometric hypothesis remains with the caller.

Source and bit conventions: `IntrinsicAlgebra/source/README.md`.
-/
