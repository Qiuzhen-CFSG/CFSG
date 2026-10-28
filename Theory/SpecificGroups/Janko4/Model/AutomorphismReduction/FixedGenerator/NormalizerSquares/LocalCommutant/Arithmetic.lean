module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Data

/-!
# Decoding the sum of packed binary matrices

Bitwise XOR is addition over the binary field. This bridges the untrusted
annihilator rows to a literal sum of matrices of actual centralizer elements.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates

theorem bit_sum_rows (L : List (Vector ℕ 112)) (i j : Fin 112) :
    bit (xorList (L.map (fun v => v.get i))) j.val =
      ((L.map decodeRows).sum) i j := by
  induction L with
  | nil => simp [xorList, bit]
  | cons v L ih =>
    simpa only [List.map_cons, List.sum_cons, xorList, bit_xor,
      Matrix.add_apply, decodeRows, bit] using congrArg (decodeRows v i j + ·) ih

theorem decode_sum_rows (L : List (Vector ℕ 112)) (r : Vector ℕ 112)
    (h : ∀ i : Fin 112, xorList (L.map (fun v => v.get i)) = r.get i) :
    (L.map decodeRows).sum = decodeRows r := by
  funext i j
  exact (bit_sum_rows L i j).symm.trans (congrArg (fun n => bit n j.val) (h i))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
