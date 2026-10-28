module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products3
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products4
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products6
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products7
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products8
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Products9
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration3
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration4
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration6
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration7
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration8
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Calibration9
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Normalization.Annihilator
import Mathlib.Tactic.FinCases

/-!
# Complete multiplication and actual-element calibration

The ten literal deviations multiply all 55 nonconstant basis elements into
`squareSpan`. Each deviation plus the identity is the restriction of the
corresponding actual local-kernel element. The imported certificates check
all rows, and their source is recorded in `KernelBound/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
open Coordinates

theorem deviation_products (i : Fin 10) (j : Fin 55) :
    deviation i * normalBasis ⟨j.val + 1, by omega⟩ ∈ squareSpan := by
  fin_cases i
  · exact deviation_products_0 j
  · exact deviation_products_1 j
  · exact deviation_products_2 j
  · exact deviation_products_3 j
  · exact deviation_products_4 j
  · exact deviation_products_5 j
  · exact deviation_products_6 j
  · exact deviation_products_7 j
  · exact deviation_products_8 j
  · exact deviation_products_9 j

theorem restriction_deviation (i : Fin 10) :
    restriction (kernelCentralizerInclusion (kernelBasis ⟨i.val + 1, by omega⟩)) =
      1 + deviation i := by
  fin_cases i
  · exact restriction_deviation_0
  · exact restriction_deviation_1
  · exact restriction_deviation_2
  · exact restriction_deviation_3
  · exact restriction_deviation_4
  · exact restriction_deviation_5
  · exact restriction_deviation_6
  · exact restriction_deviation_7
  · exact restriction_deviation_8
  · exact restriction_deviation_9

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
