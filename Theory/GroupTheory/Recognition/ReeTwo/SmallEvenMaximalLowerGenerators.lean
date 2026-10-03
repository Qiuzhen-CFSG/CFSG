module
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalBranchCertificates

/-!
# Generators of the even parity kernel

The core normal form and the even cyclic-four coordinate show that the ten
core roots together with the square of root one generate the parity kernel.
This supplies node zero's generation certificate, which is not a word closure
in the original node table.

Source: Shinoda (1975), (2.3), pp. 81–82, and `Core.normal_form`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenMaximalLower
open SmallEvenMaximalBranches

def parityGenerators : Fin 11 → SylowModel := Fin.cons (rootOne ^ 2) root

theorem parityGenerators_generate :
    Subgroup.closure (Set.range parityGenerators) = character.ker := by
  let S := Subgroup.closure (Set.range parityGenerators)
  have hsq : rootOne ^ 2 ∈ S := Subgroup.subset_closure ⟨0, rfl⟩
  have hr : ∀ i, root i ∈ S := fun i => Subgroup.subset_closure ⟨i.succ, rfl⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (by decide +kernel : rootOne ^ 2 ∈ character.ker)
    · exact character_root i
  · intro x hx
    have hc : SemidirectProduct.inl x.left ∈ S := by
      rw [← Core.normal_form x.left]
      simp only [map_mul, map_pow]
      repeat' apply S.mul_mem
      all_goals apply S.pow_mem
      all_goals exact hr _
    have ht : x.right = 1 ∨ x.right = (FiveFour.generator 4) ^ 2 :=
      (by decide +kernel : ∀ t : FiveFour.Cyclic 4,
        parity t = 1 → t = 1 ∨ t = (FiveFour.generator 4) ^ 2) x.right hx
    have he : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
      (SemidirectProduct.inl_left_mul_inr_right x).symm
    rw [he]
    apply S.mul_mem hc
    rcases ht with ht | ht
    · rw [ht, map_one]
      exact S.one_mem
    · rw [ht]
      exact (show SemidirectProduct.inr ((FiveFour.generator 4) ^ 2) = rootOne ^ 2
        by decide +kernel) ▸ hsq

end ReeTwo.SylowModel.SmallEvenMaximalLower
