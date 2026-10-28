module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.IsotropicNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Assembly

/-!
# Unconditional native zero-form witness

The checked Loewy calculation supplies the only missing premise for the
whole-normalizer transport. This leaf packages the result for either displayed
native elementary eight, preserving the literal fusion word and selected-row
conjugation maps used by the application modules.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup LargeCenterRadicals.OuterHalf

theorem nativeEight_invariant_zero_form (r : Fin 2) :
    ∃ Y : Subgroup Model, Y ≤ nativeEight r ∧ Y ≠ ⊥ ∧
      ∃ _h : IsElementaryAbelian 2 Y, Nat.card Y = 16 ∧
        intrinsicElementaryForm Y = 0 ∧
        normalizer (nativeEight r : Set Model) ≤ normalizer (Y : Set Model) := by
  let hInv : normalizer (nativeEight 0 : Set Model) ≤
      normalizer (isotropicSubgroup : Set Model) :=
    Loewy.nativeEight_normalizer_le_isotropic_normalizer
  obtain ⟨hY, hne, hc, hf, hN⟩ :=
    isotropic_pullback_properties hInv (nativeEight r) (rowFusion r)
      (rowFusion_eight r)
  exact ⟨conjugateIsotropic ((rowFusion r)⁻¹ * nativeFusion), hY, hne,
    inferInstance, hc, hf, hN⟩

end Janko4.LocalStructure.ElementaryEightGeometry
