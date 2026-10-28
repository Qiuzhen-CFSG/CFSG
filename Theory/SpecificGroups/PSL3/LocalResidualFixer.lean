module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ResidualRigidity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure

/-!
# Pointwise fixers of nonsolvable subgroups containing the binary Sylow

A pointwise fixer of the upper unitriangular subgroup is highest-root
conjugation. A nonidentity such root has centralizer in the solvable Borel.
Thus fixing a nonsolvable overgroup of that Sylow forces the automorphism
to be the identity. This applies in particular to both parabolic residuals.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751, the common-centralizer
calculation for the linear-three containing component.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full automorphism fixer of a nonsolvable subgroup containing the
specified unipotent Sylow is trivial. -/
theorem eq_one_of_fixes_nonsolvable_unipotent_overgroup
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (B : Subgroup PSL(3,F)) (hUB : unipotent F ≤ B)
    (hB : ¬ Group.IsSolvable B) (α : MulAut PSL(3,F))
    (hfix : ∀ b ∈ B, α b = b) : α = 1 := by
  obtain ⟨a,rfl⟩ := ResidualRigidity.fixer_unipotent_is_root_inner hn hF α
    (by rw [mem_fixingSubgroup_iff]; exact fun x hx => hfix x (hUB hx))
  by_cases ha : a = 0
  · subst a
    have he : (⟨0,0,0⟩ : U F) = 1 := rfl
    simp only [he,map_one]
  · have hBC : B ≤ centralizer ({projective F ⟨0,0,a⟩} : Set PSL(3,F)) := by
      intro b hb
      apply mem_centralizer_singleton_iff.mpr
      exact (mul_inv_eq_iff_eq_mul.mp (hfix b hb)).symm
    have hBB := hBC.trans (ResidualRigidity.root_centralizer_le_borel a ha)
    let := BorelStructure.borel_isSolvable F hF
    exact (hB (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hBB) (inclusion_injective hBB))).elim

end Matrix.PSL3.LinearThree
