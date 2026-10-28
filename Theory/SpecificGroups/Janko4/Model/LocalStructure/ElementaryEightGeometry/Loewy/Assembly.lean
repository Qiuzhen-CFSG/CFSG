module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Layers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Defect

/-!
# Native defect and normalizer assembly

The finite row certificates identify the actual canonical layers, while the
small image calculation identifies exactly the isotropic sixteen where the
third-layer displacement misses the fourth layer.  Combining those interfaces
turns the previously literal defect set into a normalizer invariant subgroup.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Subgroup GeneratorCertificates

theorem nativeDefectSet_eq_isotropic :
    nativeDefectSet = (isotropicSubgroup : Set Model) := by
  apply nativeDefectSet_eq_isotropic_of_layers layer_three layer_four layer_five
  intro i j
  rw [displacement_decode _ _ (toMatrix_nativeGenerator j)]
  apply congrArg decode
  rw [step3_source, step3_forward, forward3_thirdActions]

theorem nativeEight_normalizer_le_isotropic_normalizer :
    normalizer (nativeEight 0 : Set Model) ≤ normalizer (isotropicSubgroup : Set Model) := by
  rw [← nativeDefectSet_eq_isotropic]
  exact nativeDefectSet_normalizer

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
