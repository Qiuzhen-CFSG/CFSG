module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.FirstBasisProduct
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.SecondBasisProduct
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.FirstInverseProduct
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.SecondInverseProduct
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Evaluation
public import Mathlib.Order.Fin.Basic

/-!
# The literal max4 generators preserve the full binary block flag

The four imported packed products certify conjugation by the existing basis.
The actual word evaluations are reused from NormalFour.Evaluation. The zero
entries above the fifteen diagonal blocks and the monotone block labels are
then checked directly. This proves preservation of the full flag on generators;
Filtration extends it to their subgroup closure.

Source: ATLAS J4G1-max4W1 and the binary representation, attributed in
SymmetricLinear.Model and Model.Data; see OrderBound/source/README.md.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound
open GeneratorCertificates CharacteristicTwo.Coordinates
open Simplicity.Elevens.BridgeCertificate NormalFour.Certificate

lemma coordinates_first : CharacteristicTwo.coordinates CharacteristicTwo.first =
    decodeRows firstRows := by
  unfold CharacteristicTwo.coordinates
  have hx : toMatrix (CharacteristicTwo.first : Model) = m028 := image_g029
  rw [hx, m028, first_step, first_coordinates]

lemma coordinates_second : CharacteristicTwo.coordinates CharacteristicTwo.second =
    decodeRows secondRows := by
  unfold CharacteristicTwo.coordinates
  have hy : toMatrix (CharacteristicTwo.second : Model) = m025 := image_g026
  rw [hy, m025, second_step, second_coordinates]


lemma blockIndex_monotone : Monotone blockIndex := by
  rw [Fin.monotone_iff_le_succ]
  decide +kernel


private theorem blockIndex_lt (i : Fin 112) : blockIndex i < 15 := by
  revert i
  decide +kernel

private def blockOf (i : Fin 112) : Fin 15 := ⟨blockIndex i, blockIndex_lt i⟩

private def blockStart (k : Fin 16) : ℕ :=
  (⟨#[0,4,16,28,31,34,37,40,72,84,87,90,93,96,108,112], by decide⟩ :
    Vector ℕ 16).get k

private def blockEnd (i : Fin 112) : ℕ := blockStart (blockOf i).succ

private theorem blockStart_monotone : Monotone blockStart := by
  rw [Fin.monotone_iff_le_succ]
  decide +kernel

private theorem blockStart_le (i : Fin 112) :
    blockStart (blockOf i).castSucc ≤ i.val := by
  revert i
  decide +kernel

private theorem blockEnd_le (i j : Fin 112) (h : blockIndex i < blockIndex j) :
    blockEnd i ≤ j.val := by
  exact (blockStart_monotone (show (blockOf i).succ ≤ (blockOf j).castSucc from h)).trans
    (blockStart_le j)

private theorem triangular_of_row_bounds (v : Vector ℕ 112)
    (hv : ∀ i : Fin 112, v.get i < 2 ^ blockEnd i) :
    (decodeRows v).BlockTriangular (OrderDual.toDual ∘ blockIndex) := by
  intro i j hij
  have hbit : (v.get i).testBit j.val = false :=
    Nat.testBit_lt_two_pow ((hv i).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (blockEnd_le i j hij)))
  simp [decodeRows, hbit]

lemma first_triangular : (decodeRows firstRows).BlockTriangular
    (OrderDual.toDual ∘ blockIndex) :=
  triangular_of_row_bounds firstRows (by decide +kernel)

lemma second_triangular : (decodeRows secondRows).BlockTriangular
    (OrderDual.toDual ∘ blockIndex) :=
  triangular_of_row_bounds secondRows (by decide +kernel)

end Janko4.LocalStructure.SymmetricLinear.OrderBound
