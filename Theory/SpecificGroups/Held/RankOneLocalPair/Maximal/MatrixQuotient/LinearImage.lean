module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.MatrixQuotient.Data

/-!
# Generation of SL₃(2) by the max5 matrix images

The six elementary transvections are explicit short words in the two matrix
images. Diagonal-transvection elimination then proves generation of the full
matrix group; invertible diagonal entries over F₂ are one.

Source: elementary matrix elimination and the words discovered in
`MatrixQuotient/Source`. Every word identity is checked by the Lean kernel.
-/

namespace Held.RankOneLocalPair.MatrixQuotient
open Matrix.SpecialLinearGroup

private theorem transvection_word : ∀ (i j : Fin 3) (h : i ≠ j),
    ((transvectionWord i j).map generator).prod = transvection h (1 : ZMod 2) := by
  decide +kernel

private theorem binary_diag : ∀ (i j : Fin 3) (h : i ≠ j) (c : ZMod 2) (hc : c ≠ 0),
    diag2n h c hc = 1 := by decide +kernel

/-- The displayed pair generates the actual determinant-one binary matrix group. -/
public theorem matrix_generators (H : Subgroup SL) (h : ∀ k, generator k ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  apply diagonal_transvection_induction' (fun x => x ∈ H) g
  · intro i j hij c hc
    rw [binary_diag i j hij c hc]
    exact H.one_mem
  · intro i j hij c
    have hc : c = 0 ∨ c = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c
    rcases hc with rfl | rfl
    · rw [transvection_coeff_zero]
      exact H.one_mem
    · rw [← transvection_word i j hij]
      apply H.list_prod_mem
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact h k
  · intro x y hx hy
    exact H.mul_mem hx hy

end Held.RankOneLocalPair.MatrixQuotient
