module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.Wreath

/-!
# The actual two-plane wreath subgroup of Sp₄(3)

On the basis (e₀,e₁,f₀,f₁), two SL₂(3) matrices act on the orthogonal
hyperbolic planes ⟨e₀,f₀⟩ and ⟨e₁,f₁⟩. Diagonal two-by-two blocks describe
this embedding; preservation of the symplectic form follows directly from
the two determinant equations. A permutation matrix interchanges the planes.
These maps realize the entire binary tetrahedral wreath product faithfully.

The block matrix with diagonal blocks [[1,1],[2,1]] and [[2,2],[1,2]]
conjugates minus identity on the first plane to the plane swap. The source
binary tetrahedral center is matched to the literal matrix minus identity
using the unique nonidentity involution in SL₂(3), checked on that small
matrix group. No alternative symplectic carrier or abstract family tag is used.

The embedding and this marked conjugacy are precisely the hypotheses of
`exists_wreath_lift`. Combined with the group order, their image has odd
index 45 and supplies the subgroup used in the two-primary transfer proof.

Source: Aschbacher–Smith I.1.4(1), printed p.408, and GLS3 §6.1. The rank-one
matrix equivalence comes from the project's `SL2.BinaryTetrahedral` model.
-/

public section

open GLS3.Chapter5.SchurPresentation
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary

private def blockMatrix (x : SL23 × SL23) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks (Matrix.diagonal ![x.1 0 0, x.2 0 0])
    (Matrix.diagonal ![x.1 0 1, x.2 0 1])
    (Matrix.diagonal ![x.1 1 0, x.2 1 0])
    (Matrix.diagonal ![x.1 1 1, x.2 1 1])

private theorem blockMatrix_mem (x : SL23 × SL23) :
    blockMatrix x ∈ Matrix.symplecticGroup (Fin 2) (ZMod 3) := by
  have ha : x.1 0 0*x.1 1 1-x.1 0 1*x.1 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using x.1.property
  have hb : x.2 0 0*x.2 1 1-x.2 0 1*x.2 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using x.2.property
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals simp [blockMatrix, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.diagonal, Matrix.transpose_apply]
  all_goals first | linear_combination ha | linear_combination -ha |
    linear_combination hb | linear_combination -hb | ring

private def blockHom : (SL23 × SL23) →* OddPrime.Sp (ZMod 3) where
  toFun x := ⟨blockMatrix x, blockMatrix_mem x⟩
  map_one' := by apply Subtype.ext; decide
  map_mul' x y := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
    all_goals simp [blockMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.diagonal]

private theorem blockHom_injective : Function.Injective blockHom := by
  intro x y h
  have hh : blockMatrix x = blockMatrix y := congrArg Subtype.val h
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j
    · exact congrFun (congrFun hh (.inl 0)) (.inl 0)
    · exact congrFun (congrFun hh (.inl 0)) (.inr 0)
    · exact congrFun (congrFun hh (.inr 0)) (.inl 0)
    · exact congrFun (congrFun hh (.inr 0)) (.inr 0)
  · ext i j
    fin_cases i <;> fin_cases j
    · exact congrFun (congrFun hh (.inl 1)) (.inl 1)
    · exact congrFun (congrFun hh (.inl 1)) (.inr 1)
    · exact congrFun (congrFun hh (.inr 1)) (.inl 1)
    · exact congrFun (congrFun hh (.inr 1)) (.inr 1)

private def swapMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0]

private def matrixSwap : OddPrime.Sp (ZMod 3) := ⟨swapMatrix, by rw [SymplecticGroup.mem_iff]; decide⟩

private theorem matrixSwap_square : matrixSwap^2 = 1 := by
  apply Subtype.ext
  decide

private theorem matrixSwap_inverse : matrixSwap⁻¹ = matrixSwap :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using matrixSwap_square)

private theorem matrixSwap_block (x : SL23 × SL23) :
    matrixSwap * blockHom x * matrixSwap⁻¹ = blockHom x.swap := by
  rw [matrixSwap_inverse]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals simp [matrixSwap, swapMatrix, blockHom, blockMatrix, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal]

private theorem c2_cases_matrix (x : C2) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  exact (by decide : ∀ y : C2, y = 1 ∨ y = Multiplicative.ofAdd 1) x

private noncomputable def binaryBlock : (BinaryTetrahedral × BinaryTetrahedral) →* OddPrime.Sp (ZMod 3) :=
  blockHom.comp (binaryTetrahedralEquivSL.prodCongr binaryTetrahedralEquivSL).toMonoidHom

private def matrixActor : C2 →* OddPrime.Sp (ZMod 3) :=
  QuaternionGroup.cyclicPowerHom 2 matrixSwap matrixSwap_square

private theorem matrixActor_one : matrixActor (Multiplicative.ofAdd 1) = matrixSwap :=
  QuaternionGroup.cyclicPowerHom_one 2 matrixSwap matrixSwap_square

private theorem matrix_action (k : C2) :
    binaryBlock.comp (swapAction k).toMonoidHom =
      (MulAut.conj (matrixActor k)).toMonoidHom.comp binaryBlock := by
  rcases c2_cases_matrix k with rfl | rfl
  · apply MonoidHom.ext
    intro x
    simp
  · apply MonoidHom.ext
    intro x
    change blockHom (binaryTetrahedralEquivSL x.2, binaryTetrahedralEquivSL x.1) =
      matrixActor (Multiplicative.ofAdd 1) * binaryBlock x * (matrixActor (Multiplicative.ofAdd 1))⁻¹
    rw [matrixActor_one]
    exact (matrixSwap_block (binaryTetrahedralEquivSL x.1, binaryTetrahedralEquivSL x.2)).symm

/-- The two rank-one blocks and their literal plane permutation in Sp₄(3). -/
noncomputable def matrixWreath : Wreath →* OddPrime.Sp (ZMod 3) :=
  SemidirectProduct.lift binaryBlock matrixActor matrix_action

private theorem binaryBlock_injective : Function.Injective binaryBlock :=
  blockHom_injective.comp (binaryTetrahedralEquivSL.prodCongr binaryTetrahedralEquivSL).injective

theorem matrixWreath_injective : Function.Injective matrixWreath := by
  apply (MonoidHom.ker_eq_bot_iff matrixWreath).mp
  apply bot_unique
  rintro ⟨x,k⟩ hx
  change binaryBlock x * matrixActor k = 1 at hx
  rcases c2_cases_matrix k with rfl | rfl
  · rw [map_one,mul_one] at hx
    have hx1 : x = 1 := binaryBlock_injective (hx.trans (map_one binaryBlock).symm)
    subst x
    exact rfl
  · rw [matrixActor_one] at hx
    have hb : binaryBlock x = matrixSwap := by
      calc
        binaryBlock x = matrixSwap⁻¹ := eq_inv_of_mul_eq_one_left hx
        _ = matrixSwap := matrixSwap_inverse
    have h01 := congrArg (fun a : OddPrime.Sp (ZMod 3) => a.val (.inl 0) (.inl 1)) hb
    change (0 : ZMod 3) = 1 at h01
    exact (zero_ne_one h01).elim

private def minusSL : SL23 := ⟨-1,by decide⟩

private theorem binary_square_matrix : binaryTetrahedralEquivSL (binaryI^2) = minusSL := by
  have huniq : ∀ x : SL23, x ≠ 1 → x^2 = 1 → x = minusSL := by decide
  apply huniq
  · intro h
    have he : binaryI^2 = 1 := binaryTetrahedralEquivSL.injective
      (h.trans binaryTetrahedralEquivSL.map_one.symm)
    exact (by decide : binaryI^2 ≠ 1) he
  · rw [← map_pow, show (binaryI^2)^2 = 1 by decide, map_one]

private def fusionMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks !![1,1;2,1] 0 0 !![2,2;1,2]

private def fusionElement : OddPrime.Sp (ZMod 3) := ⟨fusionMatrix,by rw [SymplecticGroup.mem_iff]; decide⟩

/-- The plane swap and minus identity on one plane are conjugate in the matrix group. -/
theorem matrixWreath_fusion : ∃ g : OddPrime.Sp (ZMod 3),
    g * matrixWreath planeInvolution * g⁻¹ = matrixWreath swap := by
  have hp : matrixWreath planeInvolution = blockHom (minusSL,1) := by
    change binaryBlock (binaryI^2,1)*matrixActor 1 = _
    rw [map_one,mul_one]
    change blockHom (binaryTetrahedralEquivSL (binaryI^2),binaryTetrahedralEquivSL 1) = _
    rw [binary_square_matrix,map_one]
  have hs : matrixWreath swap = matrixSwap := by
    change binaryBlock 1 * matrixActor (Multiplicative.ofAdd 1) = _
    rw [map_one,one_mul,matrixActor_one]
  have h : fusionElement * blockHom (minusSL,1) = matrixSwap * fusionElement := by
    apply Subtype.ext
    decide
  refine ⟨fusionElement, ?_⟩
  rw [hp,hs,h,mul_inv_cancel_right]

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
