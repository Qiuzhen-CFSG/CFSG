module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Pivot

/-!
# Checks of the max4 binary-product certificate

The packed rows certify the row-prefix conditions and nonzero pivots of all
fifteen reduced words. For each pivot every later word has zero at that entry.
The generic pivot theorem proves that these conditions persist in products.

Source: ATLAS J4G1-max4W1 and the published characteristic-two basis;
see SylowTwoPart/source/README.md and KernelCardinality/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
open GeneratorCertificates OrderedBinaryProducts
lemma decode_prefix (v : Vector ℕ 28) (r : Fin 28)
    (hb : ∀ i : Fin 28, i < r → v.get i = 2 ^ i.val)
    (hd : (v.get r).testBit r.val = true)
    (ha : v.get r < 2 ^ (r.val + 1)) : RowPrefix r (decode v) := by
  constructor
  · intro i hi j
    simp [decode, bit, hb i hi, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  · simp [decode, bit, hd]
  · intro j hj
    have hz : v.get r < 2 ^ j.val := ha.trans_le
      (Nat.pow_le_pow_right (by decide) (by exact hj))
    simp [decode, bit, Nat.testBit_lt_two_pow hz]

private lemma earlier_rows : ∀ i j : Fin 15, i ≤ j → ∀ k : Fin 28,
    k < pivotRow i → (pivotRows.get j).get k = 2 ^ k.val := by decide +kernel
private lemma diagonal_bits : ∀ i j : Fin 15, i ≤ j →
    ((pivotRows.get j).get (pivotRow i)).testBit (pivotRow i).val = true := by decide +kernel
private lemma row_bounds : ∀ i j : Fin 15, i ≤ j →
    (pivotRows.get j).get (pivotRow i) < 2 ^ ((pivotRow i).val + 1) := by decide +kernel

lemma pivot_prefix (i j : Fin 15) (h : i ≤ j) :
    RowPrefix (pivotRow i) (decode (pivotRows.get j)) :=
  decode_prefix _ _ (earlier_rows i j h) (diagonal_bits i j h) (row_bounds i j h)
lemma column_lt_row (i : Fin 15) : pivotColumn i < pivotRow i := by
  revert i; decide +kernel
lemma pivot_value (i : Fin 15) : decode (pivotRows.get i) (pivotRow i) (pivotColumn i) = 1 := by
  have h : ∀ i : Fin 15,
      ((pivotRows.get i).get (pivotRow i)).testBit (pivotColumn i).val = true := by decide +kernel
  simp [decode, bit, h]
lemma later_value (i j : Fin 15) (hij : i < j) :
    decode (pivotRows.get j) (pivotRow i) (pivotColumn i) = 0 := by
  have h : ∀ i j : Fin 15, i < j →
      ((pivotRows.get j).get (pivotRow i)).testBit (pivotColumn i).val = false := by decide +kernel
  simp [decode, bit, h i j hij]
end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
