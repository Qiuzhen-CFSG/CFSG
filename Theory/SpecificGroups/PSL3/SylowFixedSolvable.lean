module
public import Theory.GroupAction.SylowFixedSolvable
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ResidualRigidity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure

/-!
# Solvable fixed groups of binary PSL₃ Sylow fixers

Every automorphism fixing the upper unipotent subgroup pointwise is a
highest-root conjugation. If nonidentity, its fixed subgroup lies in the
solvable flag Borel. Sylow conjugacy transports this to any specified Sylow
subgroup, for every finite field of order 2ⁿ, n > 0.

This is the intrinsic centralizer calculation used in the ordinary
15.1.20--21 linear branch, together with original 14.1.6 residual control.
Source: Aschbacher--Smith, E.6.8, printed pp.247--248, and 15.1.20,
printed pp.1094--1097; the root calculation is in ResidualRigidity.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- A nonidentity pointwise Sylow fixer has a solvable fixed subgroup. -/
theorem sylow_fixed_solvable {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F))
    (a : MulAut PSL(3,F)) (ha : a ≠ 1) (hfix : ∀ x ∈ S, a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card,hF]
    simp [Nat.pow_mod,Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  apply MulAut.fixed_solvable_of_sylow (unipotentSylow F hn hF) S _ a ha hfix
  intro b hb hP
  obtain ⟨c,rfl⟩ := ResidualRigidity.fixer_unipotent_is_root_inner hn hF b
    (by rw [mem_fixingSubgroup_iff]; exact hP)
  have hc : c ≠ 0 := by
    intro hc
    subst c
    have he : (⟨0,0,0⟩ : U F) = 1 := rfl
    exact hb (by simp only [he,map_one])
  have hle : (MulAut.conj (projective F ⟨0,0,c⟩)).fixedSubgroup ≤ borel F := by
    rw [MulAut.fixedSubgroup_conj]
    exact ResidualRigidity.root_centralizer_le_borel c hc
  let := BorelStructure.borel_isSolvable F hF
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
end Matrix.PSL3.LinearThree
