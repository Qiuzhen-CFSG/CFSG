module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Words
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product00
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product01
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product02
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product03
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product04
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product05
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product06
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product07
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product08
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product09
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product10
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product11
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product12
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product13
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product14
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product15
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product16
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product17
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product18
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product19
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product20
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product21
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product22
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product23
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product24
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product25
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product26
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product27
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product28
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product29
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product30
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product31
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product32
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product33
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product34
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product35
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product36
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.Product37

/-!
# A certified elementary subgroup of order 27 in the Thompson centralizer

The literal base word has cube one, and its three fixed conjugates commute.
We prove these relations in the faithful 248-dimensional binary representation,
checking every word evaluation and inverse by packed matrix products. The
already proved independent images in the actual A₉ quotient then give an
injective homomorphism from (C₃)³ into the actual max3 word subgroup.

This discharges the matrix-relation premises of the Chapter I Thompson rank
filter. It needs neither the full quotient kernel nor ambient order or
simplicity. Source: GLS3 Table 5.3x and Aschbacher--Smith A.2.19 and I.1.3.
ATLAS attribution, reproducible witnesses, and benchmarks are in `source/`.
-/

namespace Thompson.InvolutionCentralizer.ElementaryThree
open CertificateData

private def matrixMap : AlternatingQuotient.wordSubgroup →* AtlasMatrix :=
  matrixHom.comp AlternatingQuotient.wordSubgroup.subtype

private theorem matrixMap_injective : Function.Injective matrixMap := by
  intro a b h
  exact Subtype.ext (matrixHom_injective h)

private theorem image_x :
    matrixMap x = BinaryMatrix.decode 248 AlternatingQuotient.wordARows :=
  AlternatingQuotient.matrixHom_wordA

private theorem image_y :
    matrixMap y = BinaryMatrix.decode 248 AlternatingQuotient.wordBRows :=
  AlternatingQuotient.matrixHom_wordB

private theorem inverse_image {G M : Type*} [Group G] [Monoid M]
    (f : G →* M) (g : G) (a b : M) (hg : f g = a) (hab : a * b = 1) : f g⁻¹ = b := by
  calc
    f g⁻¹ = f g⁻¹ * 1 := (mul_one _).symm
    _ = f g⁻¹ * (f g * b) := by rw [hg, hab]
    _ = (f g⁻¹ * f g) * b := (mul_assoc _ _ _).symm
    _ = b := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem image_yInv : matrixMap y⁻¹ = BinaryMatrix.decode 248 yInvRows :=
  inverse_image matrixMap _ _ _ image_y yInv_right_inverse_product

-- Reassociate the published word to share the products xy and xy⁻¹.
private def rawWord : AlternatingQuotient.wordSubgroup :=
  ((x * y⁻¹) * (x * y⁻¹)) * (((x * y) * (x * y)) * (x * y)) *
    y * (x * y) * (x * y⁻¹) * (x * y)

private theorem image_raw : matrixMap rawWord = BinaryMatrix.decode 248 rawRows := by
  simp only [rawWord, map_mul, image_x, image_y, image_yInv,
    xyInv_product, xy_product, xyInv2_product, xy2_product, xy3_product,
    rawPrefix_product, rawY_product, rawXY_product, rawInv_product, raw_product]

private theorem image_base : matrixMap base = BinaryMatrix.decode 248 baseRows := by
  have h : base = (rawWord * rawWord) * (rawWord * rawWord) := by
    simp only [base, rawWord, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h]
  simp only [map_mul, image_raw, raw2_product, base_product]

private theorem image_conj1 :
    matrixMap (conjugator 1) = BinaryMatrix.decode 248 conj1Rows := by
  have h : conjugator 1 = ((y * x) * ((y * y) * (y * y))) * y := by
    change y * x * y * y * y * y * y = _
    simp only [mul_assoc]
  rw [h]
  simp only [map_mul, image_y, image_x, y2_product, y4_product, yx_product,
    conj1Prefix_product, conj1_product]

private theorem image_conj2 :
    matrixMap (conjugator 2) = BinaryMatrix.decode 248 conj2Rows := by
  have h : conjugator 2 = (((x * y) * (x * y)) * (x * y)) * y *
      ((x * y) * (x * y)) * ((y * y) * y) * (x * y) * x := by
    change x * y * x * y * x * y * y * x * y * x * y * y * y * y * x * y * x = _
    simp only [mul_assoc]
  rw [h]
  simp only [map_mul, image_x, image_y, xy_product, xy2_product, xy3_product,
    y2_product, y3_product, conj2Prefix_product, conj2Middle_product,
    conj2Y_product, conj2XY_product, conj2_product]

private theorem image_conj1Inv :
    matrixMap (conjugator 1)⁻¹ = BinaryMatrix.decode 248 conj1InvRows :=
  inverse_image matrixMap _ _ _ image_conj1 conj1Inv_right_inverse_product

private theorem image_conj2Inv :
    matrixMap (conjugator 2)⁻¹ = BinaryMatrix.decode 248 conj2InvRows :=
  inverse_image matrixMap _ _ _ image_conj2 conj2Inv_right_inverse_product

private theorem image_triple0 : matrixMap (triple 0) = BinaryMatrix.decode 248 baseRows := by
  have h : triple 0 = base := by
    change (1 : AlternatingQuotient.wordSubgroup)⁻¹ * base * 1 = base
    simp only [inv_one, one_mul, mul_one]
  rw [h]
  exact image_base

private theorem image_triple1 :
    matrixMap (triple 1) = BinaryMatrix.decode 248 triple1Rows := by
  simp only [triple, map_mul, image_conj1Inv, image_base, image_conj1,
    triple1Prefix_product, triple1_product]

private theorem image_triple2 :
    matrixMap (triple 2) = BinaryMatrix.decode 248 triple2Rows := by
  simp only [triple, map_mul, image_conj2Inv, image_base, image_conj2,
    triple2Prefix_product, triple2_product]

/-- The fixed base word is cubic in the literal max3 subgroup. -/
public theorem base_cube : base ^ 3 = 1 := by
  apply matrixMap_injective
  rw [show base ^ 3 = (base * base) * base by simp only [pow_succ, pow_zero, one_mul]]
  simp only [map_mul, image_base, map_one, base2_product, base_cube_product]

private theorem commute01 : Commute (triple 0) (triple 1) := by
  change triple 0 * triple 1 = triple 1 * triple 0
  apply matrixMap_injective
  simp only [map_mul, image_triple0, image_triple1]
  exact commute01_product.trans commute10_product.symm

private theorem commute02 : Commute (triple 0) (triple 2) := by
  change triple 0 * triple 2 = triple 2 * triple 0
  apply matrixMap_injective
  simp only [map_mul, image_triple0, image_triple2]
  exact commute02_product.trans commute20_product.symm

private theorem commute12 : Commute (triple 1) (triple 2) := by
  change triple 1 * triple 2 = triple 2 * triple 1
  apply matrixMap_injective
  simp only [map_mul, image_triple1, image_triple2]
  exact commute12_product.trans commute21_product.symm

/-- The three fixed conjugates commute in the actual matrix carrier. -/
public theorem triple_commute : ∀ i j, Commute (triple i) (triple j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact commute01
  · exact commute02
  · exact commute01.symm
  · exact Commute.refl _
  · exact commute12
  · exact commute02.symm
  · exact commute12.symm
  · exact Commute.refl _

/-- All three elements are cubic, by conjugation of the certified base. -/
public theorem triple_cube (i : Fin 3) : triple i ^ 3 = 1 :=
  triple_cube_of_base_cube base_cube i

/-- An unconditional elementary 27-subgroup embedding in the actual max3 numerator. -/
public def embedding : (Fin 3 → Multiplicative (ZMod 3)) →*
    AlternatingQuotient.wordSubgroup :=
  embeddingOfRelations base_cube triple_commute

/-- Injectivity follows from the already certified literal alternating quotient images. -/
public theorem embedding_injective : Function.Injective embedding :=
  embeddingOfRelations_injective base_cube triple_commute

end Thompson.InvolutionCentralizer.ElementaryThree
