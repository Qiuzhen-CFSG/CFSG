module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Words

/-!
# Checked free-word edges and relator endpoints

The checks are partitioned into blocks of sixteen vertices. Each edge check is
an equality of freely reduced words in the original pair. Each endpoint check
runs all six original relators on the candidate table. Neither computation
asserts subgroup membership or faithfulness of a permutation representation.

Source: the fixed table documented in `source/README.md`.
-/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
open Subgroup.CosetWordCertificate

private def Good (i : Nat) : Prop :=
  (∀ a : Letter Bool, edgeCheck i a = true) ∧
  (∀ r : Fin 6, traceEnd next i (relatorLetters r) = i)

private instance (i : Nat) : Decidable (Good i) := inferInstanceAs (Decidable (_ ∧ _))

private theorem append_good {m n : Nat}
    (hm : ∀ i : Fin m, Good i) (hn : ∀ i : Fin n, Good (m + i.val)) :
    ∀ i : Fin (m + n), Good i := by
  intro i
  by_cases hi : i.val < m
  · exact hm ⟨i.val, hi⟩
  · have h := hn ⟨i.val - m, by omega⟩
    simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hi)] using h

private theorem checked0 : ∀ i : Fin 16, Good i.val := by
  decide +kernel

private theorem checked16 : ∀ i : Fin 16, Good (16 + i.val) := by
  decide +kernel

private theorem checked32 : ∀ i : Fin 16, Good (32 + i.val) := by
  decide +kernel

private theorem checked48 : ∀ i : Fin 16, Good (48 + i.val) := by
  decide +kernel

private theorem checked64 : ∀ i : Fin 16, Good (64 + i.val) := by
  decide +kernel

private theorem checked80 : ∀ i : Fin 16, Good (80 + i.val) := by
  decide +kernel

private theorem checked96 : ∀ i : Fin 16, Good (96 + i.val) := by
  decide +kernel

private theorem checked112 : ∀ i : Fin 16, Good (112 + i.val) := by
  decide +kernel

private theorem checked128 : ∀ i : Fin 16, Good (128 + i.val) := by
  decide +kernel

private theorem checked144 : ∀ i : Fin 16, Good (144 + i.val) := by
  decide +kernel

private theorem checked160 : ∀ i : Fin 16, Good (160 + i.val) := by
  decide +kernel

private theorem checked176 : ∀ i : Fin 16, Good (176 + i.val) := by
  decide +kernel

private theorem checked192 : ∀ i : Fin 16, Good (192 + i.val) := by
  decide +kernel

private theorem checked208 : ∀ i : Fin 16, Good (208 + i.val) := by
  decide +kernel

private theorem checked224 : ∀ i : Fin 16, Good (224 + i.val) := by
  decide +kernel

private theorem checked240 : ∀ i : Fin 16, Good (240 + i.val) := by
  decide +kernel

private theorem checked256 : ∀ i : Fin 16, Good (256 + i.val) := by
  decide +kernel

private theorem checked272 : ∀ i : Fin 16, Good (272 + i.val) := by
  decide +kernel

private theorem checked288 : ∀ i : Fin 16, Good (288 + i.val) := by
  decide +kernel

private theorem checked304 : ∀ i : Fin 16, Good (304 + i.val) := by
  decide +kernel

private theorem checked320 : ∀ i : Fin 16, Good (320 + i.val) := by
  decide +kernel

private theorem checked336 : ∀ i : Fin 16, Good (336 + i.val) := by
  decide +kernel

private theorem checked352 : ∀ i : Fin 12, Good (352 + i.val) := by
  decide +kernel

private theorem all_good : ∀ i : Fin 364, Good i :=
  (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good (append_good checked0 checked16) checked32) checked48) checked64) checked80) checked96) checked112) checked128) checked144) checked160) checked176) checked192) checked208) checked224) checked240) checked256) checked272) checked288) checked304) checked320) checked336) checked352)

/-- Every encoded edge is its claimed freely reduced word. -/
theorem edges_checked (i : Fin 364) (a : Letter Bool) : edgeCheck i a = true :=
  (all_good i).1 a

/-- All six original relators return to their initial vertex. -/
theorem relators_loop (i : Fin 364) (r : Fin 6) :
    traceEnd next i (relatorLetters r) = i.val :=
  (all_good i).2 r

/-- The exact two max3 words both return to the root. -/
theorem protected_loop (b : Bool) : traceEnd next 0 (boundLetters b) = 0 := by
  revert b
  decide +kernel

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
