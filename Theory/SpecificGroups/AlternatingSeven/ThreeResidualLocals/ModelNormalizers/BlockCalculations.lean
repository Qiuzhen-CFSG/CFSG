module
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.ExpandedStructure
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic
/-!
# The four-point block stabilizer and its cubic elements

The stabilizer is the image of the faithful disjoint action of S₄ × S₃.
This supplies both its order and a 144-element parameter space for the action
checks. Natural A₄ is normalized by the whole product; diagonal A₄ exactly by
its even part. Every cubic element lies in the natural A₄ × C₃.
All finite calculations are checked by the kernel.

Source: Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section
open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

def blockHom : Perm (Fin 4) × Perm (Fin 3) →* Perm7 :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongrHom.toMonoidHom.comp
    (Perm.sumCongrHom (Fin 4) (Fin 3))

theorem blockHom_injective : Function.Injective blockHom :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongrHom.injective.comp
    Perm.sumCongrHom_injective

private theorem block_mem_iff (x : Fin 4 ⊕ Fin 3) :
    finSumFinEquiv x ∈ fourPointSet ↔ ∃ a : Fin 4, Sum.inl a = x := by
  rcases x with a | b
  · simp [fourPointSet, finSumFinEquiv]
  · simp [fourPointSet, finSumFinEquiv]

theorem blockHom_range : blockHom.range = fourPointSetwiseStabilizer := by
  apply le_antisymm
  · rintro g ⟨⟨p, q⟩, rfl⟩ a
    obtain ⟨a, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).surjective a
    simp only [blockHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      permCongrHom_coe, permCongr_apply, Equiv.symm_apply_apply, Perm.sumCongrHom_apply]
    rw [block_mem_iff, block_mem_iff]
    cases a <;> simp
  · intro g hg
    let s := (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongrHom.symm g
    have hs : s ∈ (Perm.sumCongrHom (Fin 4) (Fin 3)).range := by
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro x ⟨a, rfl⟩
      apply (block_mem_iff _).mp
      change finSumFinEquiv ((finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).symm
        (g ((finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7) (Sum.inl a)))) ∈ fourPointSet
      rw [Equiv.apply_symm_apply]
      exact (hg _).mp ((block_mem_iff _).mpr ⟨a, rfl⟩)
    obtain ⟨pq, hpq⟩ := hs
    refine ⟨pq, ?_⟩
    change (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongrHom
      (Perm.sumCongrHom (Fin 4) (Fin 3) pq) = g
    rw [hpq]
    exact (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongrHom.apply_symm_apply g

theorem fourPointSetwiseStabilizer_card : Nat.card fourPointSetwiseStabilizer = 144 := by
  rw [← blockHom_range]
  change Nat.card (Set.range blockHom) = 144
  rw [Nat.card_range_of_injective blockHom_injective, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

local instance : Fintype (Perm (Fin 4)) := fintypePerm
local instance : Fintype (Perm (Fin 3)) := fintypePerm

theorem blockHom_normalizes_natural (p : Perm (Fin 4) × Perm (Fin 3)) :
    blockHom p * naturalThree * (blockHom p)⁻¹ ∈ naturalExplicit ∧
    blockHom p * fourFlip * (blockHom p)⁻¹ ∈ naturalExplicit := by
  decide +revert +kernel

theorem blockHom_normalizes_diagonal_iff (p : Perm (Fin 4) × Perm (Fin 3)) :
    (blockHom p * diagonalThree * (blockHom p)⁻¹ ∈ diagonalExplicit ∧
    blockHom p * fourFlip * (blockHom p)⁻¹ ∈ diagonalExplicit) ↔
      blockHom p ∈ alternatingGroup (Fin 7) := by
  decide +revert +kernel

theorem blockHom_cube_mem_expanded (p : Perm (Fin 4) × Perm (Fin 3))
    (hp : blockHom p ^ 3 = 1) : blockHom p ∈ expandedFour := by
  decide +revert +kernel

end AlternatingSeven.ThreeResidualLocals
