module
public import Theory.Representation.BinaryEndpointInduction.BlockCoordinates
public import Theory.Representation.BinaryEndpointInduction.MaskCoordinates
public import Theory.Representation.BinaryEndpointInduction.IrreducibleBlock
public import Theory.Representation.BinaryEndpointInduction.ProjectionLattice
public import Theory.Representation.BinaryEndpointInduction.BlockProjections
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The exact invariant-subspace lattice of the literal spectral operator

The action is the right row action `Matrix.vecMul x (companion false)`.
Every invariant subspace is a sum of the five literal coordinate blocks.
The proof uses their distinct irreducible polynomial annihilators, rather
than a classification assumption about the induced representation.
-/
@[expose] public section
namespace BinaryEndpointInduction
open Matrix Polynomial Module
open SpectralPolynomials

/-- Vectors supported on the indicated literal spectral block. -/
def coordinateSubspace (i : Fin 5) : Submodule (ZMod 2) (Fin 45 → ZMod 2) where
  carrier := {x | ∀ j, coordinateBlock j≠i → x j=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp only [Pi.add_apply,hx j hj,hy j hj,add_zero]
  smul_mem' := by intro c x hx j hj; simp only [Pi.smul_apply,hx j hj,smul_zero]

private def blockIndex (i : Fin 5) (r : Fin (degree i)) : Fin 45 :=
  ⟨blockOffset i+r.val,by fin_cases i <;> simp [blockOffset,SpectralPolynomials.degree] at * <;> omega⟩

private theorem blockIndex_block : ∀ (i : Fin 5) (r : Fin (degree i)),
    coordinateBlock (blockIndex i r)=i := by decide +kernel

private theorem block_coord_bound : ∀ (i : Fin 5) (j : Fin 45), coordinateBlock j=i →
    blockOffset i≤j.val ∧ j.val-blockOffset i<degree i := by decide +kernel

private def blockInsert (i : Fin 5) : (Fin (degree i) → ZMod 2) →ₗ[ZMod 2] (Fin 45 → ZMod 2) where
  toFun x j := if h : coordinateBlock j=i then x ⟨j.val-blockOffset i,(block_coord_bound i j h).2⟩ else 0
  map_add' := by intro x y; ext j; by_cases h : coordinateBlock j=i <;> simp [h]
  map_smul' := by intro c x; ext j; by_cases h : coordinateBlock j=i <;> simp [h]

private def blockProject (i : Fin 5) : Module.End (ZMod 2) (Fin 45 → ZMod 2) where
  toFun x j := if coordinateBlock j=i then x j else 0
  map_add' := by intro x y; ext j; by_cases h : coordinateBlock j=i <;> simp [h]
  map_smul' := by intro c x; ext j; by_cases h : coordinateBlock j=i <;> simp [h]

private theorem blockInsert_apply_index (i : Fin 5) (x : Fin (degree i) → ZMod 2)
    (r : Fin (degree i)) : blockInsert i x (blockIndex i r)=x r := by
  change (if h : coordinateBlock (blockIndex i r)=i then
    x ⟨(blockIndex i r).val-blockOffset i,(block_coord_bound i (blockIndex i r) h).2⟩ else 0)=x r
  rw [dif_pos (blockIndex_block i r)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

private theorem blockInsert_injective (i : Fin 5) : Function.Injective (blockInsert i) := by
  intro x y h
  funext r
  simpa only [blockInsert_apply_index] using congrFun h (blockIndex i r)

private theorem blockInsert_range (i : Fin 5) : LinearMap.range (blockInsert i)=coordinateSubspace i := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩ j hj
    simp [blockInsert,hj]
  · intro hx
    refine ⟨fun r => x (blockIndex i r),?_⟩
    funext j
    by_cases hj : coordinateBlock j=i
    · simp only [blockInsert,LinearMap.coe_mk,AddHom.coe_mk,dif_pos hj]
      congr 1
      apply Fin.ext
      exact Nat.add_sub_of_le (block_coord_bound i j hj).1
    · simpa [blockInsert,hj] using (hx j hj).symm

private theorem project_range (i : Fin 5) : LinearMap.range (blockProject i) ≤ coordinateSubspace i := by
  rintro _ ⟨x,rfl⟩ j hj
  simp [blockProject,hj]

private theorem project_sum : ∑ i, blockProject i=LinearMap.id := by
  ext x j
  simp [blockProject,Finset.sum_apply,Finset.sum_ite_eq]

private theorem insert_companion (i : Fin 5) :
    (companion false).vecMulLinear.comp (blockInsert i)=
      (blockInsert i).comp (blockMatrix i).vecMulLinear := by
  apply (Pi.basisFun (ZMod 2) (Fin (degree i))).ext
  intro r
  simp only [Pi.basisFun_apply]
  exact (by decide +kernel : ∀ (i : Fin 5) (r : Fin (degree i)),
    (companion false).vecMulLinear.comp (blockInsert i) (Pi.single r 1)=
      (blockInsert i).comp (blockMatrix i).vecMulLinear (Pi.single r 1)) i r

private theorem row_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (k : ℕ) (x : Fin n → ZMod 2) :
    (A.vecMulLinear^k) x=x ᵥ* A^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    change (x ᵥ* A^k) ᵥ* A=x ᵥ* A^(k+1)
    rw [vecMul_vecMul,pow_succ]

private theorem row_aeval {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (p : (ZMod 2)[X]) (x : Fin n → ZMod 2) :
    aeval A.vecMulLinear p x=x ᵥ* aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,LinearMap.add_apply,vecMul_add,hp,hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply,
      row_pow,←vecMul_vecMul]
    simp [Algebra.algebraMap_eq_smul_one,vecMul_smul,smul_vecMul]

private theorem intertwine_aeval {V₁ V₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
    [Module (ZMod 2) V₁] [Module (ZMod 2) V₂]
    (a : Module.End (ZMod 2) V₁) (b : Module.End (ZMod 2) V₂)
    (f : V₁ →ₗ[ZMod 2] V₂) (hf : b.comp f=f.comp a)
    (p : (ZMod 2)[X]) (x : V₁) : aeval b p (f x)=f (aeval a p x) := by
  have hpow : ∀ k x, (b^k) (f x)=f ((a^k) x) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',Module.End.mul_apply,ih]
      rw [←LinearMap.comp_apply, hf, LinearMap.comp_apply]
      rw [pow_succ',Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,LinearMap.add_apply,hp,hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply,
      hpow,map_smul]

private theorem block_row_annihilated (i : Fin 5) :
    aeval (blockMatrix i).vecMulLinear (polynomial i)=0 := by
  apply LinearMap.ext
  intro x
  rw [row_aeval,block_annihilated]
  simp

private theorem coordinate_annihilated (i : Fin 5) (x : Fin 45 → ZMod 2)
    (hx : x ∈ coordinateSubspace i) :
    aeval (companion false).vecMulLinear (polynomial i) x=0 := by
  rw [←blockInsert_range] at hx
  obtain ⟨y,rfl⟩ := hx
  rw [intertwine_aeval _ _ _ (insert_companion i),block_row_annihilated]
  simp

/-- Each literal coordinate block has its displayed spectral degree. -/
theorem coordinateSubspace_finrank (i : Fin 5) :
    Module.finrank (ZMod 2) (coordinateSubspace i)=degree i := by
  rw [←blockInsert_range,LinearMap.finrank_range_of_inj (blockInsert_injective i)]
  exact Module.finrank_fin_fun (ZMod 2)

private theorem block_intersection_dichotomy
    (U : Submodule (ZMod 2) (Fin 45 → ZMod 2))
    (hU : ∀ x ∈ U, x ᵥ* companion false ∈ U) (i : Fin 5) :
    U ⊓ coordinateSubspace i=⊥ ∨ U ⊓ coordinateSubspace i=coordinateSubspace i := by
  let Z := U.comap (blockInsert i)
  have hZ : Z ∈ Module.End.invtSubmodule (blockMatrix i).vecMulLinear := by
    intro x hx
    change blockInsert i ((blockMatrix i).vecMulLinear x) ∈ U
    rw [←LinearMap.comp_apply,←insert_companion,LinearMap.comp_apply]
    exact hU _ hx
  have hd : (polynomial i).natDegree=Module.finrank (ZMod 2) (Fin (degree i) → ZMod 2) := by
    rw [SpectralPolynomials.natDegree,Module.finrank_fin_fun]
  rcases eq_bot_or_top_of_irreducible_annihilator (blockMatrix i).vecMulLinear
    (polynomial i) (SpectralPolynomials.irreducible i) (block_row_annihilated i) hd Z hZ with hz | ht
  · left
    apply le_bot_iff.mp
    intro x hx
    have hr : x ∈ LinearMap.range (blockInsert i) := (blockInsert_range i).symm ▸ hx.2
    obtain ⟨y,rfl⟩ := hr
    have hy : y ∈ Z := hx.1
    rw [hz,Submodule.mem_bot] at hy
    simp [hy]
  · right
    apply inf_eq_right.mpr
    intro x hx
    rw [←blockInsert_range] at hx
    obtain ⟨y,rfl⟩ := hx
    have hy : y ∈ Z := ht.symm ▸ Submodule.mem_top
    exact hy

/-- Every invariant subspace for the literal row companion action is the
sum of precisely the coordinate blocks that it contains. -/
theorem invariant_subspace_eq_iSup_coordinateSubspace
    (U : Submodule (ZMod 2) (Fin 45 → ZMod 2))
    (hU : ∀ x ∈ U, Matrix.vecMul x (companion false) ∈ U) :
    U=⨆ i, ⨆ (_ : coordinateSubspace i ≤ U), coordinateSubspace i := by
  apply eq_iSup_blocks_of_projection_dichotomy coordinateSubspace blockProject project_range project_sum
  · exact projections_preserve_of_coprime_annihilators (companion false).vecMulLinear
      polynomial SpectralPolynomials.pairwise_isCoprime coordinateSubspace blockProject
      project_range project_sum coordinate_annihilated U hU
  · exact block_intersection_dichotomy U hU

/-- Every invariant subspace of the row companion operator is one of the
32 literal block-mask subspaces. -/
theorem invariant_subspace_eq_maskSubspace
    (U : Submodule (ZMod 2) (Fin 45 → ZMod 2))
    (hU : ∀ x ∈ U, Matrix.vecMul x (companion false) ∈ U) :
    ∃ mask : Fin 32, U=maskSubspace mask := by
  classical
  have hmask : ∀ b : Fin 5 → Bool, ∃ m : Fin 32, ∀ i : Fin 5,
      m.val.testBit i.val=b i := by decide +kernel
  obtain ⟨m,hm⟩ := hmask (fun i => decide (coordinateSubspace i ≤ U))
  refine ⟨m,le_antisymm ?_ ?_⟩
  · rw [invariant_subspace_eq_iSup_coordinateSubspace U hU]
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro x hx j hj
    apply hx j
    intro heq
    rw [heq,hm,decide_eq_true hi] at hj
    contradiction
  · intro x hx
    have hxsum : x=∑ i, blockProject i x := by
      simpa only [LinearMap.sum_apply,LinearMap.id_apply] using
        (LinearMap.congr_fun project_sum x).symm
    rw [hxsum]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : coordinateSubspace i ≤ U
    · exact hi (project_range i ⟨x,rfl⟩)
    · have hz : blockProject i x=0 := by
        funext j
        by_cases hj : coordinateBlock j=i
        · change (if coordinateBlock j=i then x j else 0)=0
          rw [if_pos hj]
          apply hx j
          rw [hj,hm,decide_eq_false hi]
        · simp [blockProject,hj]
      rw [hz]
      exact U.zero_mem

end BinaryEndpointInduction
