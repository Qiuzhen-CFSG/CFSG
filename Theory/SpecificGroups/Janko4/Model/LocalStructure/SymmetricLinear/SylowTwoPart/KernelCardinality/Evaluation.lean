module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Restriction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Products
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.Words

/-!
# Evaluation of the max4 binary-product certificate

The given eleven full coordinate identities restrict to their small matrices.
Five checked intertwining identities then evaluate the additional right
conjugates, using the actual ATLAS output images from OrderBound.Coordinates.
The remaining products evaluate exactly word00 through word14 from Words.lean.
All image statements retain the eleven coordinate identities as a hypothesis.

Source: ATLAS J4G1-max4W1 and the published characteristic-two basis;
see SylowTwoPart/source/README.md and KernelCardinality/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
open CharacteristicTwo GeneratorCertificates
lemma restrict_decode (xs : Vector ℕ 112) (ys : Vector ℕ 28)
    (h : ∀ i : Fin 28, xs.get (Fin.castAdd 84 i) = ys.get i) :
    restrict (decodeRows xs) = decode ys := by
  ext i j
  exact congrArg (fun x => bit x j.val) (h i)

lemma image_first : representation first = decode firstRows := by
  change restrict (OrderBound.representation first) = _
  rw [OrderBound.representation_apply, OrderBound.coordinates_first]
  exact restrict_decode _ _ (by decide +kernel)

lemma image_second : representation second = decode secondRows := by
  change restrict (OrderBound.representation second) = _
  rw [OrderBound.representation_apply, OrderBound.coordinates_second]
  exact restrict_decode _ _ (by decide +kernel)

lemma conjugate_image (g u : max4Subgroup) (U V : SmallMatrix)
    (hu : representation u = U) (he : U * representation g = representation g * V) :
    representation (g⁻¹ * u * g) = V := by
  simp only [map_mul]
  rw [mul_assoc, hu, he, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private lemma initial_rows : ∀ (k : Fin 11) (i : Fin 28),
    (CharacteristicTwo.Coordinates.conjugateRows.get k).get (Fin.castAdd 84 i) =
      (qRows.get (Fin.castLE (by decide : 11 ≤ 16) k)).get i := by decide +kernel

variable (hcoord : ∀ k : Fin 11,
  coordinates (seedConjugate k.val) = decodeRows (CharacteristicTwo.Coordinates.conjugateRows.get k))

include hcoord

lemma image_initial (k : Fin 11) : representation (seedConjugate k.val) =
    decode (qRows.get (Fin.castLE (by decide : 11 ≤ 16) k)) := by
  change restrict (OrderBound.representation (seedConjugate k.val)) = _
  rw [OrderBound.representation_apply, hcoord k]
  exact restrict_decode _ _ (initial_rows k)

lemma image_conjugate11 : representation (seedConjugate 11) = decode (qRows.get 11) := by
  change representation (first⁻¹ * seedConjugate 10 * first) = _
  apply conjugate_image _ _ _ _ (image_initial hcoord (10 : Fin 11))
  rw [image_first]
  exact conjugate10_left.trans conjugate10_right.symm

lemma image_conjugate12 : representation (seedConjugate 12) = decode (qRows.get 12) := by
  change representation (second⁻¹ * seedConjugate 11 * second) = _
  apply conjugate_image _ _ _ _ (image_conjugate11 hcoord)
  rw [image_second]
  exact conjugate11_left.trans conjugate11_right.symm

lemma image_conjugate13 : representation (seedConjugate 13) = decode (qRows.get 13) := by
  change representation (first⁻¹ * seedConjugate 12 * first) = _
  apply conjugate_image _ _ _ _ (image_conjugate12 hcoord)
  rw [image_first]
  exact conjugate12_left.trans conjugate12_right.symm

lemma image_conjugate14 : representation (seedConjugate 14) = decode (qRows.get 14) := by
  change representation (second⁻¹ * seedConjugate 13 * second) = _
  apply conjugate_image _ _ _ _ (image_conjugate13 hcoord)
  rw [image_second]
  exact conjugate13_left.trans conjugate13_right.symm

lemma image_conjugate15 : representation (seedConjugate 15) = decode (qRows.get 15) := by
  change representation (first⁻¹ * seedConjugate 14 * first) = _
  apply conjugate_image _ _ _ _ (image_conjugate14 hcoord)
  rw [image_first]
  exact conjugate14_left.trans conjugate14_right.symm

def seedRepresentation : seedNormalClosure →* SmallMatrix := representation.comp seedNormalClosure.subtype

lemma image_q (k : Fin 16) : seedRepresentation (q k.val) = decode (qRows.get k) := by
  change representation (seedConjugate k.val) = _
  fin_cases k
  · exact image_initial hcoord (0 : Fin 11)
  · exact image_initial hcoord (1 : Fin 11)
  · exact image_initial hcoord (2 : Fin 11)
  · exact image_initial hcoord (3 : Fin 11)
  · exact image_initial hcoord (4 : Fin 11)
  · exact image_initial hcoord (5 : Fin 11)
  · exact image_initial hcoord (6 : Fin 11)
  · exact image_initial hcoord (7 : Fin 11)
  · exact image_initial hcoord (8 : Fin 11)
  · exact image_initial hcoord (9 : Fin 11)
  · exact image_initial hcoord (10 : Fin 11)
  · exact image_conjugate11 hcoord
  · exact image_conjugate12 hcoord
  · exact image_conjugate13 hcoord
  · exact image_conjugate14 hcoord
  · exact image_conjugate15 hcoord

lemma image_word00 : seedRepresentation word00 = decode (wordRows.get 0) := by
  exact image_q hcoord 0

lemma image_word01 : seedRepresentation word01 = decode (wordRows.get 1) := by
  change seedRepresentation (q 2 * word00) = _
  have hq : seedRepresentation (q 2) = decode (qRows.get 2) :=
    image_q hcoord 2
  simp only [map_mul, hq, image_word00 hcoord]
  rw [word1_step0]

lemma image_word02 : seedRepresentation word02 = decode (wordRows.get 2) := by
  change seedRepresentation (q 3 * word00) = _
  have hq : seedRepresentation (q 3) = decode (qRows.get 3) :=
    image_q hcoord 3
  simp only [map_mul, hq, image_word00 hcoord]
  rw [word2_step0]

lemma image_word03 : seedRepresentation word03 = decode (wordRows.get 3) := by
  change seedRepresentation (q 4 * word00) = _
  have hq : seedRepresentation (q 4) = decode (qRows.get 4) :=
    image_q hcoord 4
  simp only [map_mul, hq, image_word00 hcoord]
  rw [word3_step0]

lemma image_word04 : seedRepresentation word04 = decode (wordRows.get 4) := by
  change seedRepresentation (q 5 * word01) = _
  have hq : seedRepresentation (q 5) = decode (qRows.get 5) :=
    image_q hcoord 5
  simp only [map_mul, hq, image_word01 hcoord]
  rw [word4_step0]

lemma image_word05 : seedRepresentation word05 = decode (wordRows.get 5) := by
  change seedRepresentation (q 6 * word02) = _
  have hq : seedRepresentation (q 6) = decode (qRows.get 6) :=
    image_q hcoord 6
  simp only [map_mul, hq, image_word02 hcoord]
  rw [word5_step0]

lemma image_word06 : seedRepresentation word06 = decode (wordRows.get 6) := by
  change seedRepresentation (q 7 * word03) = _
  have hq : seedRepresentation (q 7) = decode (qRows.get 7) :=
    image_q hcoord 7
  simp only [map_mul, hq, image_word03 hcoord]
  rw [word6_step0]

lemma image_word07 : seedRepresentation word07 = decode (wordRows.get 7) := by
  change seedRepresentation (q 8 * word00 * word02) = _
  have hq : seedRepresentation (q 8) = decode (qRows.get 8) :=
    image_q hcoord 8
  simp only [map_mul, hq, image_word00 hcoord, image_word02 hcoord]
  rw [word7_step0, word7_step1]

lemma image_word08 : seedRepresentation word08 = decode (wordRows.get 8) := by
  change seedRepresentation (q 9 * word00 * word02 * word07 * word04) = _
  have hq : seedRepresentation (q 9) = decode (qRows.get 9) :=
    image_q hcoord 9
  simp only [map_mul, hq, image_word00 hcoord, image_word02 hcoord, image_word07 hcoord, image_word04 hcoord]
  rw [word8_step0, word8_step1, word8_step2, word8_step3]

lemma image_word09 : seedRepresentation word09 = decode (wordRows.get 9) := by
  change seedRepresentation (q 10 * word07) = _
  have hq : seedRepresentation (q 10) = decode (qRows.get 10) :=
    image_q hcoord 10
  simp only [map_mul, hq, image_word07 hcoord]
  rw [word9_step0]

lemma image_word10 : seedRepresentation word10 = decode (wordRows.get 10) := by
  change seedRepresentation (q 11 * word00 * word07 * word09) = _
  have hq : seedRepresentation (q 11) = decode (qRows.get 11) :=
    image_q hcoord 11
  simp only [map_mul, hq, image_word00 hcoord, image_word07 hcoord, image_word09 hcoord]
  rw [word10_step0, word10_step1, word10_step2]

lemma image_word11 : seedRepresentation word11 = decode (wordRows.get 11) := by
  change seedRepresentation (q 12 * word07 * word05 * word04 * word09) = _
  have hq : seedRepresentation (q 12) = decode (qRows.get 12) :=
    image_q hcoord 12
  simp only [map_mul, hq, image_word07 hcoord, image_word05 hcoord, image_word04 hcoord, image_word09 hcoord]
  rw [word11_step0, word11_step1, word11_step2, word11_step3]

lemma image_word12 : seedRepresentation word12 = decode (wordRows.get 12) := by
  change seedRepresentation (q 13 * word00 * word09 * word08 * word06) = _
  have hq : seedRepresentation (q 13) = decode (qRows.get 13) :=
    image_q hcoord 13
  simp only [map_mul, hq, image_word00 hcoord, image_word09 hcoord, image_word08 hcoord, image_word06 hcoord]
  rw [word12_step0, word12_step1, word12_step2, word12_step3]

lemma image_word13 : seedRepresentation word13 = decode (wordRows.get 13) := by
  change seedRepresentation (q 14 * word03 * word01 * word07 * word05 * word09 * word08 * word06) = _
  have hq : seedRepresentation (q 14) = decode (qRows.get 14) :=
    image_q hcoord 14
  simp only [map_mul, hq, image_word03 hcoord, image_word01 hcoord, image_word07 hcoord, image_word05 hcoord, image_word09 hcoord, image_word08 hcoord, image_word06 hcoord]
  rw [word13_step0, word13_step1, word13_step2, word13_step3, word13_step4, word13_step5, word13_step6]

lemma image_word14 : seedRepresentation word14 = decode (wordRows.get 14) := by
  change seedRepresentation (q 15 * word02 * word01 * word07 * word05 * word04 * word09 * word08 * word06 * word13 * word10) = _
  have hq : seedRepresentation (q 15) = decode (qRows.get 15) :=
    image_q hcoord 15
  simp only [map_mul, hq, image_word02 hcoord, image_word01 hcoord, image_word07 hcoord, image_word05 hcoord, image_word04 hcoord, image_word09 hcoord, image_word08 hcoord, image_word06 hcoord, image_word13 hcoord, image_word10 hcoord]
  rw [word14_step0, word14_step1, word14_step2, word14_step3, word14_step4, word14_step5, word14_step6, word14_step7, word14_step8, word14_step9]

lemma image_pivotWord (k : Fin 15) : seedRepresentation (pivotWord k) = decode (pivotRows.get k) := by
  fin_cases k
  · exact image_word00 hcoord
  · exact image_word02 hcoord
  · exact image_word03 hcoord
  · exact image_word01 hcoord
  · exact image_word07 hcoord
  · exact image_word05 hcoord
  · exact image_word04 hcoord
  · exact image_word09 hcoord
  · exact image_word08 hcoord
  · exact image_word11 hcoord
  · exact image_word06 hcoord
  · exact image_word12 hcoord
  · exact image_word13 hcoord
  · exact image_word10 hcoord
  · exact image_word14 hcoord

end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
