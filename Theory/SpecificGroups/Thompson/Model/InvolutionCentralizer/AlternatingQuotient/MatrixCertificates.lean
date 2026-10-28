module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.Words
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product00
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product01
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product02
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product03
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product04
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product05
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product06
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product07
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product08
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product09
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product10
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product11
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product12
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product13
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product14
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product15
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product16
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product17
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product18
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product19
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product20
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product21
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product22
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product23
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product24
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product25
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product26
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product27
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Product28

/-!
# Certified max3 words in the Thompson involution centralizer

The literal ATLAS register words have the two matrices used by the four-space
quotient construction. Each multiplication, including both inverse products,
is checked by the kernel on packed binary rows. Right-inverse uniqueness in
the faithful representation of the unit-group carrier justifies the source's
inverse steps. Checked commutation of the resulting matrices then puts the
whole generated subgroup in the centralizer of the standard involution.

This supplies the word-value and centralizer-containment inputs to the A₉
section construction, without assuming the ambient order, simplicity, or the
centralizer identification. Source: ATLAS `ThG1-max3W1`, GLS3 Table 5.3x, and
Aschbacher–Smith A.2.19. Data attribution, reproduction, and benchmark details
are in `AlternatingQuotient/source/` and `MatrixCertificates/source/`.
-/

namespace Thompson.InvolutionCentralizer.AlternatingQuotient
open MatrixCertificates

private theorem inverse_image {G M : Type*} [Group G] [Monoid M]
    (f : G →* M) (g : G) (x y : M)
    (hg : f g = x) (hxy : x * y = 1) : f g⁻¹ = y := by
  calc
    f g⁻¹ = f g⁻¹ * 1 := (mul_one _).symm
    _ = f g⁻¹ * (f g * y) := by rw [hg, hxy]
    _ = (f g⁻¹ * f g) * y := (mul_assoc _ _ _).symm
    _ = y := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem seed3_image : matrixHom seed3 = BinaryMatrix.decode 248 seed3Rows := by
  rw [seed3, map_mul, matrixHom_generatorA, matrixHom_generatorB]
  exact seed3_product

private theorem seed4_image : matrixHom seed4 = BinaryMatrix.decode 248 seed4Rows := by
  rw [seed4, map_mul, seed3_image, matrixHom_generatorB]
  exact seed4_product

private theorem seed5_image : matrixHom seed5 = BinaryMatrix.decode 248 seed5Rows := by
  rw [seed5, map_mul, seed3_image, seed4_image]
  exact seed5_product

private theorem seed6_image : matrixHom seed6 = BinaryMatrix.decode 248 seed6Rows := by
  rw [seed6, map_mul, seed3_image, seed5_image]
  exact seed6_product

private theorem seed10_image : matrixHom seed10 = BinaryMatrix.decode 248 seed10Rows := by
  simp only [seed10, map_mul, seed3_image, seed6_image, seed5_image, seed4_image]
  rw [middle_product, prefix_product]
  exact seed10_product

private theorem bLeft_image : matrixHom (generatorA * seed6) =
    BinaryMatrix.decode 248 bLeftRows := by
  rw [map_mul, matrixHom_generatorA, seed6_image]
  exact bLeft_product

private theorem bRight_image : matrixHom (seed6 * generatorA) =
    BinaryMatrix.decode 248 bRightRows := by
  rw [map_mul, seed6_image, matrixHom_generatorA]
  exact bRight_product

private theorem bBase_image :
    matrixHom ((seed6 * generatorA)⁻¹ * (generatorA * seed6)) =
      BinaryMatrix.decode 248 bBaseRows := by
  rw [map_mul, inverse_image matrixHom _ _ _ bRight_image bInverse_right_inverse_product,
    bLeft_image]
  exact bBase_product

private theorem bPower2_image :
    (BinaryMatrix.decode 248 bBaseRows) ^ 2 = BinaryMatrix.decode 248 bPower2Rows := by
  calc
    _ = (BinaryMatrix.decode 248 bBaseRows) ^ 1 *
        (BinaryMatrix.decode 248 bBaseRows) ^ 1 := pow_add _ 1 1
    _ = _ := by
      simp only [pow_one]
      exact bPower2_product

private theorem bPower4_image :
    (BinaryMatrix.decode 248 bBaseRows) ^ 4 = BinaryMatrix.decode 248 bPower4Rows := by
  calc
    _ = (BinaryMatrix.decode 248 bBaseRows) ^ 2 *
        (BinaryMatrix.decode 248 bBaseRows) ^ 2 := pow_add _ 2 2
    _ = _ := by
      simp only [bPower2_image]
      exact bPower4_product

private theorem bPower8_image :
    (BinaryMatrix.decode 248 bBaseRows) ^ 8 = BinaryMatrix.decode 248 bPower8Rows := by
  calc
    _ = (BinaryMatrix.decode 248 bBaseRows) ^ 4 *
        (BinaryMatrix.decode 248 bBaseRows) ^ 4 := pow_add _ 4 4
    _ = _ := by
      simp only [bPower4_image]
      exact bPower8_product

private theorem bPower9_image :
    (BinaryMatrix.decode 248 bBaseRows) ^ 9 = BinaryMatrix.decode 248 bPower9Rows := by
  calc
    _ = (BinaryMatrix.decode 248 bBaseRows) ^ 8 *
        (BinaryMatrix.decode 248 bBaseRows) ^ 1 := pow_add _ 8 1
    _ = _ := by
      simp only [bPower8_image, pow_one]
      exact bPower9_product

private theorem aLeft_image : matrixHom (generatorA * seed10) =
    BinaryMatrix.decode 248 aLeftRows := by
  rw [map_mul, matrixHom_generatorA, seed10_image]
  exact aLeft_product

private theorem aRight_image : matrixHom (seed10 * generatorA) =
    BinaryMatrix.decode 248 aRightRows := by
  rw [map_mul, seed10_image, matrixHom_generatorA]
  exact aRight_product

private theorem aBase_image :
    matrixHom ((seed10 * generatorA)⁻¹ * (generatorA * seed10)) =
      BinaryMatrix.decode 248 aBaseRows := by
  rw [map_mul, inverse_image matrixHom _ _ _ aRight_image aInverse_right_inverse_product,
    aLeft_image]
  exact aBase_product

private theorem aPower2_image :
    (BinaryMatrix.decode 248 aBaseRows) ^ 2 = BinaryMatrix.decode 248 aPower2Rows := by
  calc
    _ = (BinaryMatrix.decode 248 aBaseRows) ^ 1 *
        (BinaryMatrix.decode 248 aBaseRows) ^ 1 := pow_add _ 1 1
    _ = _ := by
      simp only [pow_one]
      exact aPower2_product

private theorem aPower3_image :
    (BinaryMatrix.decode 248 aBaseRows) ^ 3 = BinaryMatrix.decode 248 aPower3Rows := by
  calc
    _ = (BinaryMatrix.decode 248 aBaseRows) ^ 2 *
        (BinaryMatrix.decode 248 aBaseRows) ^ 1 := pow_add _ 2 1
    _ = _ := by
      simp only [aPower2_image, pow_one]
      exact aPower3_product

private theorem aPower6_image :
    (BinaryMatrix.decode 248 aBaseRows) ^ 6 = BinaryMatrix.decode 248 aPower6Rows := by
  calc
    _ = (BinaryMatrix.decode 248 aBaseRows) ^ 3 *
        (BinaryMatrix.decode 248 aBaseRows) ^ 3 := pow_add _ 3 3
    _ = _ := by
      simp only [aPower3_image]
      exact aPower6_product

private theorem aPower7_image :
    (BinaryMatrix.decode 248 aBaseRows) ^ 7 = BinaryMatrix.decode 248 aPower7Rows := by
  calc
    _ = (BinaryMatrix.decode 248 aBaseRows) ^ 6 *
        (BinaryMatrix.decode 248 aBaseRows) ^ 1 := pow_add _ 6 1
    _ = _ := by
      simp only [aPower6_image, pow_one]
      exact aPower7_product

private theorem aPower14_image :
    (BinaryMatrix.decode 248 aBaseRows) ^ 14 = BinaryMatrix.decode 248 wordARows := by
  calc
    _ = (BinaryMatrix.decode 248 aBaseRows) ^ 7 *
        (BinaryMatrix.decode 248 aBaseRows) ^ 7 := pow_add _ 7 7
    _ = _ := by
      simp only [aPower7_image]
      exact wordA_product

/-- The first literal max3 output has the frozen matrix used by the A₉ action. -/
public theorem matrixHom_wordA : matrixHom wordA = wordAMatrix := by
  rw [wordA, map_pow, aBase_image]
  exact aPower14_image

/-- The second literal max3 output has the frozen matrix used by the A₉ action. -/
public theorem matrixHom_wordB : matrixHom wordB = wordBMatrix := by
  rw [wordB, map_mul, map_pow, bLeft_image, bBase_image, bPower9_image]
  exact wordB_product

/-- The first literal max3 word centralizes the standard Thompson involution. -/
public theorem wordA_commute_generatorA : Commute wordA Thompson.generatorA := by
  change wordA * Thompson.generatorA = Thompson.generatorA * wordA
  apply matrixHom_injective
  simp only [map_mul, matrixHom_wordA, matrixHom_generatorA]
  exact wordATimesA_product.trans aTimesWordA_product.symm

/-- The second literal max3 word centralizes the standard Thompson involution. -/
public theorem wordB_commute_generatorA : Commute wordB Thompson.generatorA := by
  change wordB * Thompson.generatorA = Thompson.generatorA * wordB
  apply matrixHom_injective
  simp only [map_mul, matrixHom_wordB, matrixHom_generatorA]
  exact wordBTimesA_product.trans aTimesWordB_product.symm

/-- The actual source word subgroup is contained in the involution centralizer.
This discharges the containment input of the alternating-section assembly. -/
public theorem wordSubgroup_le_centralizer :
    wordSubgroup ≤ Thompson.InvolutionCentralizer.subgroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr wordA_commute_generatorA.eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr wordB_commute_generatorA.eq

end Thompson.InvolutionCentralizer.AlternatingQuotient
