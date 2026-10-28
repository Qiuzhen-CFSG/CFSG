module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks

/-!
# Solvable residuals of the two middle binary five-space parabolics

The terminal derived subgroup of the 2+3 parabolic consists of the matrices
with identity first diagonal block; for the 3+2 parabolic it consists of those
with identity last diagonal block. These are the literal kernels of the small
SL₂ diagonal-block maps defined in `Blocks`.

A refinement of `BinaryBlockGeneration` generates each kernel using only its
SL₃ transvections and upper-right transvections. A third coordinate in the
three-dimensional block expresses every such generator as a commutator inside
the same kernel, proving perfection. Each quotient embeds in SL₂(2) ≃ S₃ and
is solvable. The two containments in the terminal derived subgroup then follow
from the general solvable-residual theorems.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
Here natural flag dimensions 2 and 3 correspond to the source groups L₁ and L₃.
-/

open Matrix

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem binary_diagonal_eq_one (D : n → ZMod 2)
    (hD : det (diagonal D) ≠ 0) : diagonal D = 1 := by
  have hn : ∀ i, D i ≠ 0 := by
    simpa only [det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies] using hD
  have hbin : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have he : D = fun _ => 1 := funext fun i => hbin (D i) (hn i)
  rw [he, diagonal_one]

/-- Block elimination can omit either diagonal family of transvections when
that diagonal block is the identity. -/
private theorem binary_block_induction_fixed (P : Matrix (n ⊕ m) (n ⊕ m) (ZMod 2) → Prop)
    (hone : P 1) (hmul : ∀ A B, P A → P B → P (A * B))
    (hupper : ∀ (i : n) (j : m) c,
      P (transvection (Sum.inl i) (Sum.inr j) c))
    (A : Matrix n n (ZMod 2)) (B : Matrix n m (ZMod 2)) (D : Matrix m m (ZMod 2))
    (hleft : A = 1 ∨ ∀ (i j : n) (_hij : i ≠ j) c,
      P (transvection (Sum.inl i) (Sum.inl j) c))
    (hright : D = 1 ∨ ∀ (i j : m) (_hij : i ≠ j) c,
      P (transvection (Sum.inr i) (Sum.inr j) c))
    (hdet : det (fromBlocks A B 0 D) ≠ 0) : P (fromBlocks A B 0 D) := by
  have hdets : det A ≠ 0 ∧ det D ≠ 0 := by
    simpa only [det_fromBlocks_zero₂₁, ne_eq, mul_eq_zero, not_or] using hdet
  have hA : P (fromBlocks A 0 0 (1 : Matrix m m (ZMod 2))) := by
    rcases hleft with rfl | hleft
    · simpa using hone
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun A => P (fromBlocks A 0 0 (1 : Matrix m m (ZMod 2)))) A hdets.1
    · intro d hd
      simpa [binary_diagonal_eq_one d hd] using hone
    · intro t
      rw [← TransvectionStruct.toMatrix_sumInl]
      exact hleft t.i t.j t.hij t.c
    · intro X Y _ _ hX hY
      simpa [fromBlocks_multiply] using hmul _ _ hX hY
  have hD : P (fromBlocks (1 : Matrix n n (ZMod 2)) 0 0 D) := by
    rcases hright with rfl | hright
    · simpa using hone
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun D => P (fromBlocks (1 : Matrix n n (ZMod 2)) 0 0 D)) D hdets.2
    · intro d hd
      simpa [binary_diagonal_eq_one d hd] using hone
    · intro t
      have he : fromBlocks (1 : Matrix n n (ZMod 2)) 0 0 t.toMatrix =
          transvection (Sum.inr t.i) (Sum.inr t.j) t.c := by
        ext i j
        cases i <;> cases j <;>
          simp [transvection, TransvectionStruct.toMatrix, single, one_apply]
      rw [he]
      exact hright t.i t.j t.hij t.c
    · intro X Y _ _ hX hY
      simpa [fromBlocks_multiply] using hmul _ _ hX hY
  have hU (C : Matrix n m (ZMod 2)) :
      P (fromBlocks (1 : Matrix n n (ZMod 2)) C 0 (1 : Matrix m m (ZMod 2))) := by
    induction C using Matrix.induction_on' with
    | h_zero => simpa using hone
    | h_add X Y hX hY =>
      simpa [fromBlocks_multiply, add_comm] using hmul _ _ hX hY
    | h_std_basis i j c =>
      have he : fromBlocks (1 : Matrix n n (ZMod 2)) (single i j c) 0
          (1 : Matrix m m (ZMod 2)) = transvection (Sum.inl i) (Sum.inr j) c := by
        ext r s
        cases r <;> cases s <;> simp [transvection, single, one_apply]
      rw [he]
      exact hupper i j c
  have hinv : D⁻¹ * D = 1 := nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hdets.2)
  have hf : fromBlocks A B 0 D =
      fromBlocks (1 : Matrix n n (ZMod 2)) (B * D⁻¹) 0 (1 : Matrix m m (ZMod 2)) *
        (fromBlocks A 0 0 (1 : Matrix m m (ZMod 2)) *
          fromBlocks (1 : Matrix n n (ZMod 2)) 0 0 D) := by
    simp [fromBlocks_multiply, Matrix.mul_assoc, hinv]
  rw [hf]
  exact hmul _ _ (hU _) (hmul _ _ hA hD)
end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem binary_partition_induction_fixed (p : n → Prop) [DecidablePred p]
    (P : Matrix n n (ZMod 2) → Prop)
    (hone : P 1) (hmul : ∀ A B, P A → P B → P (A * B))
    (hupper : ∀ (i j : n), p i → ¬ p j → ∀ c, P (transvection i j c))
    (M : Matrix n n (ZMod 2)) (hdet : det M ≠ 0)
    (hzero : ∀ i j, ¬p i → p j → M i j = 0)
    (hleft : (∀ i j, p i → p j → M i j = (1 : Matrix n n (ZMod 2)) i j) ∨
      ∀ i j, i ≠ j → p i → p j → ∀ c, P (transvection i j c))
    (hright : (∀ i j, ¬p i → ¬p j → M i j = (1 : Matrix n n (ZMod 2)) i j) ∨
      ∀ i j, i ≠ j → ¬p i → ¬p j → ∀ c, P (transvection i j c)) : P M := by
  let e := Equiv.sumCompl p
  let R := reindexAlgEquiv (ZMod 2) (ZMod 2) e
  let N := M.submatrix e e
  have hN : N = fromBlocks (toBlocks₁₁ N) (toBlocks₁₂ N) 0 (toBlocks₂₂ N) := by
    have hz : toBlocks₂₁ N = 0 := by
      ext i j
      exact hzero i.val j.val i.property j.property
    conv_lhs => rw [← fromBlocks_toBlocks N, hz]
  have ht (i j : {i // p i} ⊕ {i // ¬p i}) (hij : i ≠ j) (c : ZMod 2) :
      R (transvection i j c) = transvection (e i) (e j) c := by
    exact (TransvectionStruct.toMatrix_reindexEquiv e
      (⟨i, j, hij, c⟩ : TransvectionStruct _ (ZMod 2))).symm
  have hh : P (R N) := by
    rw [hN]
    apply binary_block_induction_fixed (fun X => P (R X))
    · simpa using hone
    · intro A B hA hB
      simpa using hmul (R A) (R B) hA hB
    · intro i j c
      rw [ht _ _ Sum.inl_ne_inr]
      exact hupper _ _ i.property j.property c
    · rcases hleft with hleft | hleft
      · left
        ext i j
        change M i.val j.val = _
        rw [hleft _ _ i.property j.property]
        simp [one_apply, Subtype.ext_iff]
      · right
        intro i j hij c
        rw [ht _ _ (Sum.inl_injective.ne hij)]
        exact hleft _ _ (Subtype.val_injective.ne hij) i.property j.property c
    · rcases hright with hright | hright
      · left
        ext i j
        change M i.val j.val = _
        rw [hright _ _ i.property j.property]
        simp [one_apply, Subtype.ext_iff]
      · right
        intro i j hij c
        rw [ht _ _ (Sum.inr_injective.ne hij)]
        exact hright _ _ (Subtype.val_injective.ne hij) i.property j.property c
    · rw [← hN]
      simpa only [N, det_submatrix_equiv_self] using hdet
  have he : R N = M := by
    ext i j
    change M (e (e.symm i)) (e (e.symm j)) = M i j
    simp
  rwa [he] at hh
end Matrix

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Subgroup
open scoped commutatorElement

private def twoGenerators : Set Group :=
  {g | ∃ (i j : Fin 5) (hij : i ≠ j) (c : ZMod 2),
    2 ≤ j.val ∧ g = Matrix.SpecialLinearGroup.transvection hij c}

private def threeGenerators : Set Group :=
  {g | ∃ (i j : Fin 5) (hij : i ≠ j) (c : ZMod 2),
    i.val < 3 ∧ g = Matrix.SpecialLinearGroup.transvection hij c}

private theorem transvection_mem_parabolic (k : ℕ) (i j : Fin 5) (hij : i ≠ j)
    (c : ZMod 2) (hp : j.val < k → i.val < k) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ parabolic k := by
  rw [parabolic_eq_closure_transvections]
  exact subset_closure ⟨i, j, hij, c, hp, rfl⟩

private theorem two_generator_mem (i j : Fin 5) (hij : i ≠ j) (c : ZMod 2)
    (hj : 2 ≤ j.val) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ parabolicTwoLargeBlock := by
  have hp := transvection_mem_parabolic 2 i j hij c (by omega)
  refine ⟨⟨_, hp⟩, ?_, rfl⟩
  change parabolicTwoSmallBlock ⟨_, hp⟩ = 1
  apply Subtype.ext
  ext a b
  rw [parabolicTwoSmallBlock_entry]
  have hjb : j.val ≠ b.val := by have := b.isLt; omega
  simp [Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single, Matrix.one_apply, Fin.ext_iff, hjb]

private theorem three_generator_mem (i j : Fin 5) (hij : i ≠ j) (c : ZMod 2)
    (hi : i.val < 3) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ parabolicThreeLargeBlock := by
  have hp := transvection_mem_parabolic 3 i j hij c (fun _ => hi)
  refine ⟨⟨_, hp⟩, ?_, rfl⟩
  change parabolicThreeSmallBlock ⟨_, hp⟩ = 1
  apply Subtype.ext
  ext a b
  rw [parabolicThreeSmallBlock_entry]
  have hia : i.val ≠ 3 + a.val := by omega
  simp [Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single, Matrix.one_apply, Fin.ext_iff, hia]

private theorem two_eq_closure : parabolicTwoLargeBlock = closure twoGenerators := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    let H := closure twoGenerators
    have hs : parabolicTwoSmallBlock x = 1 := hx
    have hz := (mem_parabolic_iff_lowerLeft_zero 2 x.val).mp x.property
    have hex : ∃ h : Group, h ∈ H ∧ h.val = x.val.val := by
      apply Matrix.binary_partition_induction_fixed (fun i : Fin 5 => i.val < 2)
        (fun M => ∃ h : Group, h ∈ H ∧ h.val = M)
      · exact ⟨1, H.one_mem, rfl⟩
      · rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, H.mul_mem ha hb, rfl⟩
      · intro i j hi hj c
        have hij : i ≠ j := by intro h; subst j; contradiction
        exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
          subset_closure ⟨i, j, hij, c, by omega, rfl⟩, rfl⟩
      · rw [x.val.property]
        exact one_ne_zero
      · intro i j hi hj
        exact hz i j (by omega) hj
      · left
        intro i j hi hj
        have h := parabolicTwoSmallBlock_entry x ⟨i.val, hi⟩ ⟨j.val, hj⟩
        rw [hs] at h
        simpa [Matrix.one_apply, Fin.ext_iff] using h.symm
      · right
        intro i j hij hi hj c
        exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
          subset_closure ⟨i, j, hij, c, by omega, rfl⟩, rfl⟩
    obtain ⟨h, hh, he⟩ := hex
    change x.val ∈ H
    exact (Subtype.ext he : h = x.val) ▸ hh
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, c, hj, rfl⟩
    exact two_generator_mem i j hij c hj

private theorem three_eq_closure : parabolicThreeLargeBlock = closure threeGenerators := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    let H := closure threeGenerators
    have hs : parabolicThreeSmallBlock x = 1 := hx
    have hz := (mem_parabolic_iff_lowerLeft_zero 3 x.val).mp x.property
    have hex : ∃ h : Group, h ∈ H ∧ h.val = x.val.val := by
      apply Matrix.binary_partition_induction_fixed (fun i : Fin 5 => i.val < 3)
        (fun M => ∃ h : Group, h ∈ H ∧ h.val = M)
      · exact ⟨1, H.one_mem, rfl⟩
      · rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, H.mul_mem ha hb, rfl⟩
      · intro i j hi hj c
        have hij : i ≠ j := by intro h; subst j; contradiction
        exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
          subset_closure ⟨i, j, hij, c, hi, rfl⟩, rfl⟩
      · rw [x.val.property]
        exact one_ne_zero
      · intro i j hi hj
        exact hz i j (by omega) hj
      · right
        intro i j hij hi hj c
        exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
          subset_closure ⟨i, j, hij, c, hi, rfl⟩, rfl⟩
      · left
        intro i j hi hj
        have h := parabolicThreeSmallBlock_entry x ⟨i.val-3, by omega⟩ ⟨j.val-3, by omega⟩
        rw [hs] at h
        have he : i.val - 3 = j.val - 3 ↔ i.val = j.val := by omega
        simpa [Matrix.one_apply, Fin.ext_iff, Nat.add_sub_of_le (by omega : 3 ≤ i.val),
          Nat.add_sub_of_le (by omega : 3 ≤ j.val),
          he] using h.symm
    obtain ⟨h, hh, he⟩ := hex
    change x.val ∈ H
    exact (Subtype.ext he : h = x.val) ▸ hh
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, c, hi, rfl⟩
    exact three_generator_mem i j hij c hi

private theorem middle_elementary_commutator (i s j : Fin 5)
    (his : i ≠ s) (hsj : s ≠ j) (hij : i ≠ j) :
    ⁅elementary i s, elementary s j⁆ = elementary i j := by
  rw [commutatorElement_def,
    inv_eq_of_mul_eq_one_left (elementary_square i s),
    inv_eq_of_mul_eq_one_left (elementary_square s j)]
  calc
    elementary i s * elementary s j * elementary i s * elementary s j =
        (elementary i s * (elementary s j * elementary i s)) * elementary s j := by
      simp only [mul_assoc]
    _ = (elementary s j * elementary i j) * elementary s j := by
      rw [elementary_steinberg i s j his hsj hij]
    _ = elementary i j := by
      rw [elementary_commute s j i j hsj hij.symm, mul_assoc,
        elementary_square, mul_one]

/-- The identity-small-block kernel in the 2+3 parabolic is perfect. -/
instance parabolicTwoLargeBlock_isPerfect : Group.IsPerfect parabolicTwoLargeBlock := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm parabolicTwoLargeBlock.commutator_le_self
  conv_lhs => rw [two_eq_closure]
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, c, hj, rfl⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  obtain ⟨s, his, hsj, hs⟩ := (by decide : ∀ i j : Fin 5, i ≠ j → 2 ≤ j.val →
    ∃ s : Fin 5, i ≠ s ∧ s ≠ j ∧ 2 ≤ s.val) i j hij hj
  have h₁ : elementary i s ∈ parabolicTwoLargeBlock := by
    simpa [elementary, his] using two_generator_mem i s his 1 hs
  have h₂ : elementary s j ∈ parabolicTwoLargeBlock := by
    simpa [elementary, hsj] using two_generator_mem s j hsj 1 hj
  have h := commutator_mem_commutator h₁ h₂
  rw [middle_elementary_commutator i s j his hsj hij] at h
  simpa [elementary, hij] using h

/-- The identity-small-block kernel in the 3+2 parabolic is perfect. -/
instance parabolicThreeLargeBlock_isPerfect : Group.IsPerfect parabolicThreeLargeBlock := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm parabolicThreeLargeBlock.commutator_le_self
  conv_lhs => rw [three_eq_closure]
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, c, hi, rfl⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  obtain ⟨s, his, hsj, hs⟩ := (by decide : ∀ i j : Fin 5, i ≠ j → i.val < 3 →
    ∃ s : Fin 5, i ≠ s ∧ s ≠ j ∧ s.val < 3) i j hij hi
  have h₁ : elementary i s ∈ parabolicThreeLargeBlock := by
    simpa [elementary, his] using three_generator_mem i s his 1 hi
  have h₂ : elementary s j ∈ parabolicThreeLargeBlock := by
    simpa [elementary, hsj] using three_generator_mem s j hsj 1 hs
  have h := commutator_mem_commutator h₁ h₂
  rw [middle_elementary_commutator i s j his hsj hij] at h
  simpa [elementary, hij] using h

private theorem middle_slTwo_isSolvable :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The quotient of the 2+3 parabolic by its identity-small-block kernel is solvable. -/
instance parabolicTwoSmallBlock_quotient_isSolvable :
    Group.IsSolvable (parabolic 2 ⧸ parabolicTwoSmallBlock.ker) := by
  let := middle_slTwo_isSolvable
  exact Group.isSolvable_of_isSolvable_injective
    (QuotientGroup.kerLift_injective parabolicTwoSmallBlock)

/-- The quotient of the 3+2 parabolic by its identity-small-block kernel is solvable. -/
instance parabolicThreeSmallBlock_quotient_isSolvable :
    Group.IsSolvable (parabolic 3 ⧸ parabolicThreeSmallBlock.ker) := by
  let := middle_slTwo_isSolvable
  exact Group.isSolvable_of_isSolvable_injective
    (QuotientGroup.kerLift_injective parabolicThreeSmallBlock)

/-- The terminal derived subgroup used in source clause (1) is the kernel of the
literal first two-dimensional diagonal block. -/
@[simp] theorem parabolicResidual_two : parabolicResidual 2 = parabolicTwoLargeBlock := by
  apply le_antisymm
  · exact map_mono (solvableResidual_le_of_solvable_quotient parabolicTwoSmallBlock.ker)
  · exact le_map_solvableResidual_of_isPerfect _ _ parabolicTwoLargeBlock_le

/-- The terminal derived subgroup used in source clause (2) is the kernel of the
literal last two-dimensional diagonal block. -/
@[simp] theorem parabolicResidual_three : parabolicResidual 3 = parabolicThreeLargeBlock := by
  apply le_antisymm
  · exact map_mono (solvableResidual_le_of_solvable_quotient parabolicThreeSmallBlock.ker)
  · exact le_map_solvableResidual_of_isPerfect _ _ parabolicThreeLargeBlock_le

end Representation.SL5ExteriorSquare
