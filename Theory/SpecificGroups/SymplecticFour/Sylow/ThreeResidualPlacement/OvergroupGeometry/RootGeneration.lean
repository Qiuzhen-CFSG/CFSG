module
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-!
# Generating symplectic four-space from one opposite long root

The positive root groups and the first lower long-root group generate the
actual matrix group in characteristic two. The long-root Weyl element
supplies both lower short roots; the mixed-root Weyl element supplies the
second lower long root. The eight-root generation theorem then applies.

This is the root-generation step in the intrinsic Sylow-overgroup placement
used for Aschbacher–Smith, Lemma 15.3.28, printed p.1131 (PDF p.1148), with
B.5.5–6, printed pp.104–105. Root indices are those of
`Theory.Representation.FirstCohomologySymplecticFour.Generation`.
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.OvergroupGeometry
variable {K : Type*} [Field K] [CharP K 2]

private def longSwap : Sp K := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def pairSwap : Sp K := rootElement 6 1 * rootElement 7 1 * rootElement 6 1

private lemma longSwap_val : (longSwap (K := K)).val =
    fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1] := by
  change rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1 = _
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single, CharTwo.add_self_eq_zero]

private lemma pairSwap_val : (pairSwap (K := K)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, CharTwo.neg_eq,
      CharTwo.add_self_eq_zero]

private lemma seventh_root (t : K) : rootElement 7 t =
    longSwap * rootElement 4 t * longSwap := by
  apply Subtype.ext
  change rootMatrix 7 t = (longSwap (K := K)).val * rootMatrix 4 t * (longSwap (K := K)).val
  rw [longSwap_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Matrix.single,
      vecHead, vecTail, CharTwo.neg_eq]

private lemma fifth_root (t : K) : rootElement 5 t =
    longSwap * rootElement 6 t * longSwap := by
  apply Subtype.ext
  change rootMatrix 5 t = (longSwap (K := K)).val * rootMatrix 6 t * (longSwap (K := K)).val
  rw [longSwap_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.single, CharTwo.neg_eq]

private lemma third_root (t : K) : rootElement 3 t =
    pairSwap * rootElement 1 t * pairSwap := by
  apply Subtype.ext
  change rootMatrix 3 t = (pairSwap (K := K)).val * rootMatrix 1 t * (pairSwap (K := K)).val
  rw [pairSwap_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.single]

/-- The unipotent subgroup and the opposite first long root generate Sp₄. -/
theorem eq_top_of_unipotent_le_of_opposite_long_root (H : Subgroup (Sp K))
    (hU : unipotent ≤ H) (h₁ : ∀ t : K, rootElement 1 t ∈ H) : H = ⊤ := by
  have h₀ (t : K) : rootElement 0 t ∈ H := hU (positive_root_mem_unipotent 0 t (by simp))
  have h₂ (t : K) : rootElement 2 t ∈ H := hU (positive_root_mem_unipotent 2 t (by simp))
  have h₄ (t : K) : rootElement 4 t ∈ H := hU (positive_root_mem_unipotent 4 t (by simp))
  have h₆ (t : K) : rootElement 6 t ∈ H := hU (positive_root_mem_unipotent 6 t (by simp))
  have hw : longSwap (K := K) ∈ H := H.mul_mem (H.mul_mem (h₀ 1) (h₁ 1)) (h₀ 1)
  have h₇ (t : K) : rootElement 7 t ∈ H := by
    rw [seventh_root]
    exact H.mul_mem (H.mul_mem hw (h₄ t)) hw
  have h₅ (t : K) : rootElement 5 t ∈ H := by
    rw [fifth_root]
    exact H.mul_mem (H.mul_mem hw (h₆ t)) hw
  have hw' : pairSwap (K := K) ∈ H := H.mul_mem (H.mul_mem (h₆ 1) (h₇ 1)) (h₆ 1)
  have h₃ (t : K) : rootElement 3 t ∈ H := by
    rw [third_root]
    exact H.mul_mem (H.mul_mem hw' (h₁ t)) hw'
  apply eq_top_of_rootElement_mem
  intro r t
  fin_cases r
  · exact h₀ t
  · exact h₁ t
  · exact h₂ t
  · exact h₃ t
  · exact h₄ t
  · exact h₅ t
  · exact h₆ t
  · exact h₇ t

end Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.OvergroupGeometry
