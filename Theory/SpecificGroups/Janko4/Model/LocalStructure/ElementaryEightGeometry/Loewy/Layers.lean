module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.LayerCertificates0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.LayerCertificates1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.LayerCertificates2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.LayerCertificates3

/-!
# The native canonical commutator layers

Forward and reverse row certificates identify every successive span for the
original 112-dimensional row action of the native elementary eight. The final
four-space is fixed pointwise, making displacement on the third layer additive
in the elementary actor. Source: KW (1988), Corollary 2.3.6.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open GeneratorCertificates

theorem layer_one : layer (nativeEight 0) 1 = rowSpan layer1Rows := by
  have hs := next_layer_eq_step 0 packedOne step0Rows (by exact rowSpan_one.symm)
    (fun i j => (displacement_decode _ _ (toMatrix_nativeGenerator j) _).trans
      (congrArg decode (step0_source i j)))
  exact hs.trans (rowSpan_eq_of_certificates _ _ _ _ step0_forward step0_reverse)

theorem layer_two : layer (nativeEight 0) 2 = rowSpan layer2Rows := by
  have hs := next_layer_eq_step 1 layer1Rows step1Rows layer_one
    (fun i j => (displacement_decode _ _ (toMatrix_nativeGenerator j) _).trans
      (congrArg decode (step1_source i j)))
  exact hs.trans (rowSpan_eq_of_certificates _ _ _ _ step1_forward step1_reverse)

theorem layer_three : layer (nativeEight 0) 3 = rowSpan layer3Rows := by
  have hs := next_layer_eq_step 2 layer2Rows step2Rows layer_two
    (fun i j => (displacement_decode _ _ (toMatrix_nativeGenerator j) _).trans
      (congrArg decode (step2_source i j)))
  exact hs.trans (rowSpan_eq_of_certificates _ _ _ _ step2_forward step2_reverse)

theorem layer_four : layer (nativeEight 0) 4 = rowSpan layer4Rows := by
  have hs := next_layer_eq_step 3 layer3Rows step3Rows layer_three
    (fun i j => (displacement_decode _ _ (toMatrix_nativeGenerator j) _).trans
      (congrArg decode (step3_source i j)))
  exact hs.trans (rowSpan_eq_of_certificates _ _ _ _ step3_forward step3_reverse)

private theorem layer4_fixed : ∀ i : Fin 4, ∀ j : Fin 8,
    packedRow (layer4Rows.get i) (generatorRows j) ^^^ layer4Rows.get i = 0 := by
  decide +kernel

theorem layer_five : layer (nativeEight 0) 5 = ⊥ := by
  rw [next_layer_rows 4 layer4Rows layer_four]
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i,j⟩,rfl⟩
  change displacement (nativeGenerator j) (decode (layer4Rows.get i)) = 0
  rw [displacement_decode _ _ (toMatrix_nativeGenerator j),layer4_fixed]
  funext k
  simp [decode,bit]

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
