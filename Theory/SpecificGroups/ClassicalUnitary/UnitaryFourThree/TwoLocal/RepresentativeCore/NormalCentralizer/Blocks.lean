module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The two block shapes of a projective involution centralizer lift

A lift either preserves the two eigenspaces of diag(-1,-1,1,1), or
interchanges them. In each case its nonzero blocks are unitary planes.
We retain both cases in the parametrization used for the quaternion core.

The shape calculation adapts the retained `StandardCentralizerBound/Blocks`
experiment and agrees with the calculation in `RepresentativeBound`.
Source conventions: GLS3, chapter 2, §2.7; application: Aschbacher–Smith,
condition E and Theorem 0.1.2(4), printed pp.3–4.
-/

@[expose] public section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer

abbrev U₂ := Matrix.unitaryGroup (Fin 2) FiniteField.Nine
private abbrev U₄ := Matrix.unitaryGroup (Fin 4) FiniteField.Nine

def swap : Mat₄ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
theorem swap_sq : swap * swap = 1 := by decide
private theorem star_swap : star swap = swap := by decide
private theorem swap_anti : swap * standardInvolutionMatrix = -(standardInvolutionMatrix * swap) := by decide

private theorem block_star (A B : Mat₂) : star (block A B) = block (star A) (star B) :=
  block_adj A B

private def top (A : Mat₄) : Mat₂ := fun i j => A (Fin.castAdd 2 i) (Fin.castAdd 2 j)
private def bot (A : Mat₄) : Mat₂ := fun i j => A (Fin.natAdd 2 i) (Fin.natAdd 2 j)

private theorem top_block (A B : Mat₂) : top (block A B) = A := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl
private theorem bot_block (A B : Mat₂) : bot (block A B) = B := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl

private theorem commute_shape (A : Mat₄) (h : A * standardInvolutionMatrix = standardInvolutionMatrix * A) : A = block (top A) (bot A) := by
  have hneg (x : FiniteField.Nine) : -x = x ↔ x = 0 := by revert x; decide
  have hneg' (x : FiniteField.Nine) : x = -x ↔ x = 0 := by revert x; decide
  have hh (i j : Fin 4) := congrArg (fun B : Mat₄ => B i j) h
  simp only [standardInvolutionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
  apply Matrix.ext; intro i j
  have hij := hh i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | simpa [block, top, bot, hneg, hneg'] using hij


private def blockUnitary (A B : U₂) : U₄ := ⟨block A.val B.val, by
  rw [Matrix.mem_unitaryGroup_iff', block_star, block_mul,
    Matrix.mem_unitaryGroup_iff'.mp A.property, Matrix.mem_unitaryGroup_iff'.mp B.property,
    block_one]⟩
private def swapUnitary : U₄ := ⟨swap, by rw [Matrix.mem_unitaryGroup_iff', star_swap, swap_sq]⟩

private theorem commute_exists (g : U₄) (h : g.val * standardInvolutionMatrix = standardInvolutionMatrix * g.val) :
    ∃ A B : U₂, g.val = block A.val B.val := by
  have hs := commute_shape g.val h
  have hu := Matrix.mem_unitaryGroup_iff'.mp g.property
  rw [hs, block_star, block_mul, ← block_one] at hu
  have hA : top g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [top_block] using congrArg top hu
  have hB : bot g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [bot_block] using congrArg bot hu
  exact ⟨⟨top g.val, hA⟩, ⟨bot g.val, hB⟩, hs⟩

/-- Both commuting and anticommuting lifts are included. -/
private theorem unitary_block_shape (g : U₄)
    (h : g.val * standardInvolutionMatrix = standardInvolutionMatrix * g.val ∨ g.val * standardInvolutionMatrix = -(standardInvolutionMatrix * g.val)) :
    ∃ A B : U₂, g.val = block A.val B.val ∨ g.val = block A.val B.val * swap := by
  rcases h with h | h
  · obtain ⟨A, B, he⟩ := commute_exists g h
    exact ⟨A, B, Or.inl he⟩
  · have hh : (g * swapUnitary).val * standardInvolutionMatrix = standardInvolutionMatrix * (g * swapUnitary).val := by
      change (g.val * swap) * standardInvolutionMatrix = standardInvolutionMatrix * (g.val * swap)
      rw [mul_assoc, swap_anti, mul_neg, ← mul_assoc, h, neg_mul, neg_neg, mul_assoc]
    obtain ⟨A, B, he⟩ := commute_exists (g * swapUnitary) hh
    refine ⟨A, B, Or.inr ?_⟩
    rw [← he]
    change g.val = (g.val * swap) * swap
    rw [mul_assoc, swap_sq, mul_one]

/-- The matrix of an SU element is unitary for the identity form. -/
private def toUnitary (g : (form 4).specialSubgroup) : U₄ :=
  ⟨g.val.val, by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.1
    change star g.val.val * 1 * g.val.val = 1 at h
    simpa only [mul_one] using h⟩

theorem special_block_shape (g : (form 4).specialSubgroup)
    (h : project 4 g ∈ standardCentralizer) :
    ∃ A B : U₂, g.val.val = block A.val B.val ∨
      g.val.val = block A.val B.val * swap :=
  unitary_block_shape (toUnitary g) ((project_mem_standardCentralizer_iff g).mp h)

theorem swap_block (A B : Mat₂) : swap * block A B = block B A * swap := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, block, Matrix.mul_apply, Fin.sum_univ_succ]

theorem block_scalar (u : FiniteField.Nine) :
    block (Matrix.scalar (Fin 2) u) (Matrix.scalar (Fin 2) u) =
      Matrix.scalar (Fin 4) u := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem block_ext {A B C E : Mat₂} (h : block A B = block C E) : A = C ∧ B = E :=
  ⟨by simpa only [top_block] using congrArg top h,
   by simpa only [bot_block] using congrArg bot h⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer
