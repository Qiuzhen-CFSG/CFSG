module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.Words
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct00
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct01
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct02
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct03
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct04
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct05
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct06
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct07
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct08
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct09
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct10
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct11
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct12
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct13
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct14
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct15
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct16
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct17
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct18
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicProduct19

/-!
# A certified elementary subgroup of order 27 in the Lyons involution subgroup

The fixed base word has cube one, and its three specified conjugates commute.
Twenty carry-free matrix product certificates establish these relations in the
faithful ATLAS representation. Intertwining identities identify the conjugates
without requiring new inverse certificates. The existing alternating quotient
then detects independence and makes the resulting homomorphism injective.

Source: GLS3, Lyons involution table (printed p.278), as used in
Aschbacher--Smith A.2.19 and I.1.3. ATLAS attribution, candidate generation,
and the kernel-checking boundary are recorded in `source/README.md`.
-/

namespace Lyons.SimplicityCertificate.InvolutionElementaryThree

open Atlas111WordCertificate LocalCommutant.Words MatrixCertificate

private def representation : involutionLocalSubgroup →* AtlasMatrix :=
  matrixRepresentation.comp involutionLocalSubgroup.subtype

private theorem representation_injective : Function.Injective representation :=
  matrixRepresentation_injective.comp Subtype.val_injective

private theorem image_x : representation x = abMatrix := image_localA

private theorem image_y : representation y = localBMatrix := image_localB

private theorem image_seed :
    representation (x * y * x * x * x * x * x * x * y) = seedMatrix := by
  have h6 : abMatrix * abMatrix * abMatrix * abMatrix * abMatrix * abMatrix =
      ab6Matrix := by
    calc
      _ = (abMatrix * abMatrix * abMatrix) * (abMatrix * abMatrix * abMatrix) := by
        simp only [mul_assoc]
      _ = ab6Matrix := by rw [mul_ab2, mul_ab3, mul_ab6]
  simp only [map_mul, image_x, image_y]
  calc
    _ = abMatrix * localBMatrix *
        (abMatrix * abMatrix * abMatrix * abMatrix * abMatrix * abMatrix) *
        localBMatrix := by simp only [mul_assoc]
    _ = seedMatrix := by rw [h6, mul_xy, mul_xyx6, mul_seed]

private theorem image_base : representation base = cubicMatrix := by
  rw [base, map_pow, image_seed]
  calc
    _ = (seedMatrix * seedMatrix) * (seedMatrix * seedMatrix) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = cubicMatrix := by rw [mul_seed2, mul_cubic]

/-- The literal base word has cube one in the actual involution subgroup. -/
public theorem base_cube : base ^ 3 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, image_base]
  calc
    _ = (cubicMatrix * cubicMatrix) * cubicMatrix := by
      simp only [pow_succ, pow_zero, one_mul]
    _ = 1 := by rw [mul_cubic2, mul_cube, oneMatrix_eq]

private theorem image_conjugate (w b : involutionLocalSubgroup) (m : AtlasMatrix)
    (h : representation b * representation w = representation w * m) :
    representation (w⁻¹ * b * w) = m := by
  calc
    _ = representation (w⁻¹) * (representation b * representation w) := by
      simp only [map_mul, mul_assoc]
    _ = representation (w⁻¹) * (representation w * m) := by rw [h]
    _ = m := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem image_triple_zero : representation (triple 0) = cubicMatrix := by
  change representation (1⁻¹ * base * 1) = cubicMatrix
  simpa only [inv_one, one_mul, mul_one] using image_base

private theorem image_triple_one : representation (triple 1) = secondMatrix := by
  change representation (y⁻¹ * base * y) = secondMatrix
  apply image_conjugate
  rw [image_base, image_y, mul_cy, mul_ySecond]

private theorem image_conjugator_two :
    representation (y * x * x * y * x) = conjugatingMatrix := by
  simp only [map_mul, image_x, image_y]
  calc
    _ = localBMatrix * (abMatrix * abMatrix) * localBMatrix * abMatrix := by
      simp only [mul_assoc]
    _ = conjugatingMatrix := by rw [mul_ab2, mul_yx2, mul_yx2y, mul_conjugating]

private theorem image_triple_two : representation (triple 2) = thirdMatrix := by
  change representation ((y * x * x * y * x)⁻¹ * base * (y * x * x * y * x)) = _
  apply image_conjugate
  rw [image_base, image_conjugator_two, mul_cw, mul_wThird]

private theorem commute_zero_one : Commute (triple 0) (triple 1) := by
  apply representation_injective
  simp only [map_mul, image_triple_zero, image_triple_one]
  exact mul_pair01.trans mul_pair01rev.symm

private theorem commute_zero_two : Commute (triple 0) (triple 2) := by
  apply representation_injective
  simp only [map_mul, image_triple_zero, image_triple_two]
  exact mul_pair02.trans mul_pair02rev.symm

private theorem commute_one_two : Commute (triple 1) (triple 2) := by
  apply representation_injective
  simp only [map_mul, image_triple_one, image_triple_two]
  exact mul_pair12.trans mul_pair12rev.symm

/-- The three fixed literal cubic conjugates commute pairwise. -/
public theorem triple_commute : ∀ i j, Commute (triple i) (triple j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact commute_zero_one
  · exact commute_zero_two
  · exact commute_zero_one.symm
  · exact Commute.refl _
  · exact commute_one_two
  · exact commute_zero_two.symm
  · exact commute_one_two.symm
  · exact Commute.refl _

/-- The certified elementary homomorphism into the literal involution subgroup. -/
public def embedding :
    (Fin 3 → Multiplicative (ZMod 3)) →* involutionLocalSubgroup :=
  embeddingOfRelations base_cube triple_commute

/-- The actual alternating quotient detects all three independent coordinates. -/
public theorem embedding_injective : Function.Injective embedding :=
  embeddingOfRelations_injective base_cube triple_commute

end Lyons.SimplicityCertificate.InvolutionElementaryThree
