module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Checks
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Augmentation

/-!
# The three augmentation layers

Extracting a packed 100-coordinate slice preserves exactly its matrix entries.
The checked slices show upper triangularity and ten consecutive, unmixed copies
of the actual augmentation matrix on each of the three diagonal blocks.
Source witnesses: `../source/filtration.json`; Aschbacher–Smith G.7.3(2).
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
open Packed

private theorem bit_of_shift_zero (v m r : ℕ) (h : v >>> m = 0) (hm : m ≤ r) : bit v r = 0 := by
  have hb := congrArg (fun x => bit x (r - m)) h
  simpa only [bit, Nat.testBit_shiftRight, Nat.add_sub_of_le hm, Nat.zero_testBit,
    Bool.false_eq_true, ↓reduceIte] using hb

private theorem bit_slice (v m n r : ℕ) (hr : r < n) :
    bit ((v >>> m) % 2 ^ n) r = bit v (m + r) := by
  simp [bit, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, hr]

private theorem bit_shift_copy (v : ℕ) (hv : v < 2 ^ 10) (a b r : Fin 10) :
    bit (v <<< (10 * b.val)) (10 * a.val + r.val) = if a = b then bit v r.val else 0 := by
  by_cases hab : a = b
  · subst a
    simp [bit, Nat.testBit_shiftLeft]
  · rw [if_neg hab]
    have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have h : ¬ 10 * a.val + r.val ≥ 10 * b.val := by omega
      simp [bit, Nat.testBit_shiftLeft, h]
    · have h : 10 ≤ 10 * a.val + r.val - 10 * b.val := by omega
      have hp : 2 ^ 10 ≤ 2 ^ (10 * a.val + r.val - 10 * b.val) :=
        Nat.pow_le_pow_of_le (by decide) h
      have hz := Nat.testBit_lt_two_pow (hv.trans_le hp)
      simp [bit, Nat.testBit_shiftLeft, hz]

/-- Entries strictly below the three 100-dimensional blocks vanish. -/
theorem lower_blocks (s : Fin 2) (r j : Fin 300) (h : j.val / 100 < r.val / 100) :
    transformedMatrix s r j = 0 := by
  apply bit_of_shift_zero _ (100 * (j.val / 100 + 1)) r.val
  · exact (all_columns j).2.2.1 s
  · omega

/-- Every diagonal block is ten copies of the actual augmentation action. -/
theorem diagonal_blocks (s : Fin 2) (layer : Fin 3) (a b r j : Fin 10) :
    transformedMatrix s (coordinate layer a r) (coordinate layer b j) =
      if a = b then augmentationMatrix (CertificateData.generator s) r j else 0 := by
  have h := (all_columns (coordinate layer b j)).2.2.2 s
  have hl : (coordinate layer b j).val / 100 = layer.val := by dsimp [coordinate]; omega
  have hj : (coordinate layer b j).val % 10 = j.val := by dsimp [coordinate]; omega
  have hc : ((coordinate layer b j).val % 100) / 10 = b.val := by dsimp [coordinate]; omega
  simp only [hl, hc] at h
  have hp : (⟨(coordinate layer b j).val % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10) = j :=
    Fin.ext hj
  rw [hp] at h
  change bit (transformedColumns s)[(coordinate layer b j).val]!
    (100 * layer.val + 10 * a.val + r.val) = _
  rw [show 100 * layer.val + 10 * a.val + r.val = 100 * layer.val + (10 * a.val + r.val)
    by omega, ← bit_slice _ _ 100 _ (by omega), h,
    bit_shift_copy _ (pointColumns_bound s j), pointColumns_actual]
end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
