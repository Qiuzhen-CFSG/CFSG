module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Data
/-!
# Checked quadratic compatibility inside the Mathieu Sylow groups

Each displacement matrix is checked using reduced coordinate vectors. A rejected
commuting pair has a certified nonzero entry of its double displacement; for
M22 this entry is reduced modulo the actual pair line. Every compatible pair
of distinct nonidentity vertices has at most four common neighbors.
Source: Aschbacher--Smith K.4, printed pp.458--459.
-/
@[expose] public section
namespace MathieuCode.QuadraticActors
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
set_option maxRecDepth 4096

def matrix_checkRow (v : Fin 192) : Prop := pointMatrix (vertexPoint v) = matrix v

private theorem matrix_check_00 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_01 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_02 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_03 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_04 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_05 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_06 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_07 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_08 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_09 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 9 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_10 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 10 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_11 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 11 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_12 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 12 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_13 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 13 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_14 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 14 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_15 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 15 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_16 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 16 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_17 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 17 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_18 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 18 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_19 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 19 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_20 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 20 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_21 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 21 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_22 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 22 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

private theorem matrix_check_23 : ∀ a : Fin 8, matrix_checkRow ⟨8 * 23 + a.val, by omega⟩ := by
  unfold matrix_checkRow
  decide +kernel

theorem matrix_check (v : Fin 192) : matrix_checkRow v := by
  have blocks : ∀ (b : Fin 24) (a : Fin 8), matrix_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact matrix_check_00
    · exact matrix_check_01
    · exact matrix_check_02
    · exact matrix_check_03
    · exact matrix_check_04
    · exact matrix_check_05
    · exact matrix_check_06
    · exact matrix_check_07
    · exact matrix_check_08
    · exact matrix_check_09
    · exact matrix_check_10
    · exact matrix_check_11
    · exact matrix_check_12
    · exact matrix_check_13
    · exact matrix_check_14
    · exact matrix_check_15
    · exact matrix_check_16
    · exact matrix_check_17
    · exact matrix_check_18
    · exact matrix_check_19
    · exact matrix_check_20
    · exact matrix_check_21
    · exact matrix_check_22
    · exact matrix_check_23
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

def outer_matrix_checkRow (v : Fin 72) : Prop := pointMatrix (outerPoint v) = outerMatrix v

private theorem outer_matrix_check_00 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_01 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_02 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_03 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_04 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_05 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_06 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_07 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

private theorem outer_matrix_check_08 : ∀ a : Fin 8, outer_matrix_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold outer_matrix_checkRow
  decide +kernel

theorem outer_matrix_check (v : Fin 72) : outer_matrix_checkRow v := by
  have blocks : ∀ (b : Fin 9) (a : Fin 8), outer_matrix_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact outer_matrix_check_00
    · exact outer_matrix_check_01
    · exact outer_matrix_check_02
    · exact outer_matrix_check_03
    · exact outer_matrix_check_04
    · exact outer_matrix_check_05
    · exact outer_matrix_check_06
    · exact outer_matrix_check_07
    · exact outer_matrix_check_08
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

def rejection_checkRow (v : Fin 192) : Prop := ∀ w : Fin 192, compatible v w = false ∨ adjacent v w = true ∨
    (matrix v * matrix w) (rejectRow v w) (rejectCol v w) ≠ 0

private theorem rejection_check_00 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_01 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_02 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_03 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_04 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_05 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_06 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_07 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_08 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_09 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 9 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_10 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 10 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_11 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 11 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_12 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 12 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_13 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 13 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_14 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 14 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_15 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 15 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_16 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 16 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_17 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 17 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_18 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 18 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_19 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 19 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_20 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 20 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_21 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 21 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_22 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 22 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

private theorem rejection_check_23 : ∀ a : Fin 8, rejection_checkRow ⟨8 * 23 + a.val, by omega⟩ := by
  unfold rejection_checkRow
  decide +kernel

theorem rejection_check (v : Fin 192) : rejection_checkRow v := by
  have blocks : ∀ (b : Fin 24) (a : Fin 8), rejection_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact rejection_check_00
    · exact rejection_check_01
    · exact rejection_check_02
    · exact rejection_check_03
    · exact rejection_check_04
    · exact rejection_check_05
    · exact rejection_check_06
    · exact rejection_check_07
    · exact rejection_check_08
    · exact rejection_check_09
    · exact rejection_check_10
    · exact rejection_check_11
    · exact rejection_check_12
    · exact rejection_check_13
    · exact rejection_check_14
    · exact rejection_check_15
    · exact rejection_check_16
    · exact rejection_check_17
    · exact rejection_check_18
    · exact rejection_check_19
    · exact rejection_check_20
    · exact rejection_check_21
    · exact rejection_check_22
    · exact rejection_check_23
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

def outer_rejection_checkRow (v : Fin 72) : Prop := ∀ w : Fin 72,
    compatible (outerVertex v) (outerVertex w) = false ∨ outerAdjacent v w = true ∨
    (outerMatrix v * outerMatrix w) (outerRejectRow v w) (outerRejectCol v w) -
      (outerMatrix v * outerMatrix w) 0 (outerRejectCol v w) *
        pairCoordinate (outerRejectRow v w) ≠ 0

private theorem outer_rejection_check_00 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_01 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_02 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_03 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_04 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_05 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_06 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_07 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

private theorem outer_rejection_check_08 : ∀ a : Fin 8, outer_rejection_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold outer_rejection_checkRow
  decide +kernel

theorem outer_rejection_check (v : Fin 72) : outer_rejection_checkRow v := by
  have blocks : ∀ (b : Fin 9) (a : Fin 8), outer_rejection_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact outer_rejection_check_00
    · exact outer_rejection_check_01
    · exact outer_rejection_check_02
    · exact outer_rejection_check_03
    · exact outer_rejection_check_04
    · exact outer_rejection_check_05
    · exact outer_rejection_check_06
    · exact outer_rejection_check_07
    · exact outer_rejection_check_08
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

def neighbors_checkRow (v : Fin 192) : Prop := ∀ w : Fin 192, v ≠ 0 → w ≠ 0 → w ≠ v → adjacent v w = true →
    (Finset.univ.filter (fun k : Fin 192 => adjacent v k && adjacent w k)).card ≤ 4

private theorem neighbors_check_00 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_01 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_02 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_03 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_04 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_05 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_06 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_07 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_08 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_09 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 9 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_10 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 10 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_11 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 11 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_12 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 12 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_13 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 13 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_14 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 14 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_15 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 15 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_16 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 16 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_17 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 17 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_18 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 18 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_19 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 19 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_20 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 20 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_21 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 21 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_22 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 22 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

private theorem neighbors_check_23 : ∀ a : Fin 8, neighbors_checkRow ⟨8 * 23 + a.val, by omega⟩ := by
  unfold neighbors_checkRow
  decide +kernel

theorem neighbors_check (v : Fin 192) : neighbors_checkRow v := by
  have blocks : ∀ (b : Fin 24) (a : Fin 8), neighbors_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact neighbors_check_00
    · exact neighbors_check_01
    · exact neighbors_check_02
    · exact neighbors_check_03
    · exact neighbors_check_04
    · exact neighbors_check_05
    · exact neighbors_check_06
    · exact neighbors_check_07
    · exact neighbors_check_08
    · exact neighbors_check_09
    · exact neighbors_check_10
    · exact neighbors_check_11
    · exact neighbors_check_12
    · exact neighbors_check_13
    · exact neighbors_check_14
    · exact neighbors_check_15
    · exact neighbors_check_16
    · exact neighbors_check_17
    · exact neighbors_check_18
    · exact neighbors_check_19
    · exact neighbors_check_20
    · exact neighbors_check_21
    · exact neighbors_check_22
    · exact neighbors_check_23
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

def outer_neighbors_checkRow (v : Fin 72) : Prop := ∀ w : Fin 72, v ≠ 0 → w ≠ 0 → w ≠ v → outerAdjacent v w = true →
    (Finset.univ.filter (fun k : Fin 72 => outerAdjacent v k && outerAdjacent w k)).card ≤ 4

private theorem outer_neighbors_check_00 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_01 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_02 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_03 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_04 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_05 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_06 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_07 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

private theorem outer_neighbors_check_08 : ∀ a : Fin 8, outer_neighbors_checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold outer_neighbors_checkRow
  decide +kernel

theorem outer_neighbors_check (v : Fin 72) : outer_neighbors_checkRow v := by
  have blocks : ∀ (b : Fin 9) (a : Fin 8), outer_neighbors_checkRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact outer_neighbors_check_00
    · exact outer_neighbors_check_01
    · exact outer_neighbors_check_02
    · exact outer_neighbors_check_03
    · exact outer_neighbors_check_04
    · exact outer_neighbors_check_05
    · exact outer_neighbors_check_06
    · exact outer_neighbors_check_07
    · exact outer_neighbors_check_08
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  simpa only [he] using h

theorem outer_vertex_coverage : ∀ v : Fin 192,
    ((vertexPoint v 0 = 0 ∧ vertexPoint v 11 = 11) ∨
      (vertexPoint v 0 = 11 ∧ vertexPoint v 11 = 0)) → outerVertex (outerCode v) = v := by
  decide +kernel

end MathieuCode.QuadraticActors
