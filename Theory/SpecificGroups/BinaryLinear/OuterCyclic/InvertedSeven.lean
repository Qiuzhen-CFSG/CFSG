module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# An inverted seven in the binary three- and four-dimensional automizers

The displayed symmetric binary matrix has order seven; adjoining an
identity block gives the four-dimensional case. Inverse transpose inverts
this matrix, and therefore conjugates its inner automorphism to its inverse.
The actual projective-to-special-linear equivalence transports both actors.
All matrix identities are checked by the kernel.

Source application: Aschbacher--Smith H.9.1(4) and 12.1.1,
printed pp.390 and788. No automorphism classification is required.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups

namespace BinaryLinear.OuterCyclic
private def sevenThree : SL(3,ZMod 2) :=
  ⟨!![0,1,0; 1,0,1; 0,1,1], by decide +kernel⟩
private def sevenFour : SL(4,ZMod 2) :=
  ⟨!![0,1,0,0; 1,0,1,0; 0,1,1,0; 0,0,0,1], by decide +kernel⟩

private theorem symmetric_seven (n : ℕ) (hn : n = 3 ∨ n = 4) :
    ∃ x : SL(n,ZMod 2), orderOf x = 7 ∧ Matrix.SpecialLinearGroup.transpose x = x := by
  have make {m : ℕ} (x : SL(m,ZMod 2)) (hp : x ^ 7 = 1) (hne : x ≠ 1)
      (hs : Matrix.SpecialLinearGroup.transpose x = x) :
      orderOf x = 7 ∧ Matrix.SpecialLinearGroup.transpose x = x := by
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact ⟨orderOf_eq_prime hp hne,hs⟩
  rcases hn with rfl | rfl
  · refine ⟨sevenThree,make _ ?_ ?_ ?_⟩
    · apply Subtype.ext
      decide +kernel
    · decide +kernel
    · apply Subtype.ext
      decide +kernel
  · refine ⟨sevenFour,make _ ?_ ?_ ?_⟩
    · apply Subtype.ext
      decide +kernel
    · decide +kernel
    · apply Subtype.ext
      decide +kernel

/-- Each full automizer contains a real element of order seven. -/
theorem aut_binary_real_seven (n : ℕ) (hn : n = 3 ∨ n = 4) :
    ∃ x : MulAut (PSL(n,ZMod 2)), orderOf x = 7 ∧ IsConj x x⁻¹ := by
  obtain ⟨x,hx,hs⟩ := symmetric_seven n hn
  have hn0 : 0 < n := by rcases hn with rfl | rfl <;> decide
  have hi := MulAut.conj_injective_of_center_eq_bot (binary_center_eq_bot hn0)
  let e := MulAut.congr (projectiveEquivSL hn0).symm
  refine ⟨e (MulAut.conj x), ?_, ?_⟩
  · rw [e.orderOf_eq, orderOf_injective MulAut.conj hi, hx]
  · apply isConj_iff.mpr
    refine ⟨e (graphSL n),?_⟩
    rw [← map_inv,← map_mul,← map_inv,← map_mul]
    congr 1
    apply MulEquiv.ext
    intro y
    change graphSL n (x * (graphSL n)⁻¹ y * x⁻¹) = x⁻¹ * y * x
    rw [map_mul,map_mul,map_inv]
    have hg : graphSL n x = x⁻¹ := by change (Matrix.SpecialLinearGroup.transpose x)⁻¹ = x⁻¹; rw [hs]
    rw [hg,MulAut.apply_inv_self,inv_inv]
end BinaryLinear.OuterCyclic

