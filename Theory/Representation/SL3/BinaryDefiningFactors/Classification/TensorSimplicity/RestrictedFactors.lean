module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Certificate
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.NaturalCertificate
public import Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.FinCases

/-!
# Simplicity of the concrete binary restricted SL₃ factors

The binary cycle and shear generate the entire matrix algebra on the natural
and trace-zero adjoint spaces. We transport the checked binary certificates by
pulling back a coefficient-field subalgebra along entrywise scalar extension.
Explicit coordinates verify the two generators on the actual adjoint action.
The dual uses inverse-transpose generators in its dual basis. Matrix-algebra
density then proves simplicity, over any field of characteristic two.

The final trivial tensor factor is removed by an actual representation
equivalence. This also gives simplicity and separation of one-letter words.
It does not establish simplicity of longer Frobenius tensor words.

Source: GLS III, 2.8.10(c). The coordinates and certificates are adapted from
Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates,
NaturalCertificate and Certificate; those files certify the binary actions.
-/

public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixGroups
open Matrix
namespace Representation.SL3.BinaryDefiningFactors
namespace TensorSimplicity
variable {F K : Type*} [Field F] [Field K] [CharP F 2] [CharP K 2]

private abbrev binaryScalarStructure : Algebra (ZMod 2) K := ZMod.algebra K 2
attribute [local instance] binaryScalarStructure

private theorem binaryMatrixAlgebra (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (hd : ∀ P : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
      A ∈ P → B ∈ P → P = ⊤)
    (Q : Subalgebra K (Matrix (Fin d) (Fin d) K))
    (hA : A.map (algebraMap (ZMod 2) K) ∈ Q)
    (hB : B.map (algebraMap (ZMod 2) K) ∈ Q) : Q = ⊤ := by
  let f := (Algebra.ofId (ZMod 2) K).mapMatrix (m := Fin d)
  let P := (Q.restrictScalars (ZMod 2)).comap f
  have hP : P = ⊤ := hd P hA hB
  have hunit (i j : Fin d) : Matrix.single i j (1 : K) ∈ Q := by
    have hm : Matrix.single i j (1 : ZMod 2) ∈ P := by rw [hP]; trivial
    change (Matrix.single i j (1 : ZMod 2)).map (algebraMap (ZMod 2) K) ∈ Q at hm
    simpa [Matrix.map_single] using hm
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply Q.sum_mem
  intro i _
  apply Q.sum_mem
  intro j _
  simpa using Q.smul_mem (hunit i j) (M i j)

omit [CharP F 2] in
private theorem density_of_binary_generators
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K SL(3,F) V) {d : ℕ}
    (e : Module.End K V ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (a b : SL(3,F)) (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (ha : e (ρ a) = A.map (algebraMap (ZMod 2) K))
    (hb : e (ρ b) = B.map (algebraMap (ZMod 2) K))
    (hd : ∀ P : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
      A ∈ P → B ∈ P → P = ⊤) :
    Algebra.adjoin K (Set.range ρ) = ⊤ := by
  let P := Algebra.adjoin K (Set.range ρ)
  let Q := P.map e.toAlgHom
  have haQ : A.map (algebraMap (ZMod 2) K) ∈ Q := by
    rw [← ha]
    exact ⟨ρ a, Algebra.subset_adjoin (Set.mem_range_self a), rfl⟩
  have hbQ : B.map (algebraMap (ZMod 2) K) ∈ Q := by
    rw [← hb]
    exact ⟨ρ b, Algebra.subset_adjoin (Set.mem_range_self b), rfl⟩
  have hQ := binaryMatrixAlgebra d A B hd Q haQ hbQ
  apply top_unique
  intro f _
  have hf : e f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

private def cycle : SL(3,F) := ⟨!![0,0,1;1,0,0;0,1,0], by simp [Matrix.det_fin_three]⟩
private def shear : SL(3,F) := ⟨!![1,1,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩

omit [CharP F 2] in
private theorem natural_density (ι : F →+* K) :
    Algebra.adjoin K (Set.range (natural ι)) = ⊤ := by
  apply density_of_binary_generators (natural ι) LinearMap.toMatrixAlgEquiv'
    cycle shear BinaryLinearThree.IrreducibleCatalogue.cycle.val
    BinaryLinearThree.IrreducibleCatalogue.shear.val
  · change LinearMap.toMatrix' (Matrix.toLin' _) = _
    rw [LinearMap.toMatrix'_toLin']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycle, BinaryLinearThree.IrreducibleCatalogue.cycle, Matrix.map_apply]
  · change LinearMap.toMatrix' (Matrix.toLin' _) = _
    rw [LinearMap.toMatrix'_toLin']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shear, BinaryLinearThree.IrreducibleCatalogue.shear, Matrix.map_apply]
  · exact BinaryLinearThree.IrreducibleCatalogue.NaturalCertificate.matrix_algebra_eq_top

private def matrixOf (v : Fin 8 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![v 6, v 0, v 1; v 2, v 7, v 3; v 4, v 5, v 6 + v 7]

private def readMatrix (a : Matrix (Fin 3) (Fin 3) K) : Fin 8 → K :=
  ![a 0 1, a 0 2, a 1 0, a 1 2, a 2 0, a 2 1, a 0 0, a 1 1]

private theorem matrixOf_trace (v : Fin 8 → K) : (matrixOf v).trace = 0 := by
  simp [matrixOf, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem matrixOf_readMatrix (a : Matrix (Fin 3) (Fin 3) K)
    (ha : a.trace = 0) : matrixOf (readMatrix a) = a := by
  have hdiag : a 0 0 + a 1 1 = a 2 2 := by
    have he : a 0 0 + a 1 1 + a 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ha
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
      congrArg (fun x => x + a 2 2) he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf, readMatrix, hdiag]

private def coordinates : AdjointSpace K ≃ₗ[K] (Fin 8 → K) where
  toFun f := readMatrix (LinearMap.toMatrix' f.val)
  invFun v := ⟨(matrixOf v).toLin', by
    change (LinearMap.trace K (Fin 3 → K)) (matrixOf v).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact matrixOf_trace v⟩
  left_inv f := by
    apply Subtype.ext
    change (matrixOf (readMatrix (LinearMap.toMatrix' f.val))).toLin' = f.val
    rw [matrixOf_readMatrix, Matrix.toLin'_toMatrix']
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact f.property
  right_inv v := by
    change readMatrix (LinearMap.toMatrix' (matrixOf v).toLin') = v
    rw [LinearMap.toMatrix'_toLin']
    funext i
    fin_cases i <;> rfl
  map_add' f h := by
    change readMatrix (LinearMap.toMatrix' (f.val + h.val)) = _
    rw [map_add]
    funext i
    fin_cases i <;> rfl
  map_smul' c f := by
    change readMatrix (LinearMap.toMatrix' (c • f.val)) = _
    rw [map_smul]
    funext i
    fin_cases i <;> rfl

private def adjointMatrixEquiv :
    Module.End K (AdjointSpace K) ≃ₐ[K] Matrix (Fin 8) (Fin 8) K :=
  (coordinates.conjAlgEquiv K).trans LinearMap.toMatrixAlgEquiv'

omit [CharP F 2] in
private theorem cycle_inv : (cycle (F := F))⁻¹ = cycle * cycle := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, Matrix.mul_apply, Fin.sum_univ_three]

private theorem shear_inv : (shear (F := F))⁻¹ = shear := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, Matrix.mul_apply, Fin.sum_univ_three,
      CharTwo.add_self_eq_zero]

omit [CharP F 2] in
private theorem adjoint_cycle (ι : F →+* K) :
    adjointMatrixEquiv (factorRep ι .adjoint cycle) =
      BinaryLinearThree.IrreducibleCatalogue.cycleMatrix.map (algebraMap (ZMod 2) K) := by
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix' (coordinates.conj
    (factorRep ι .adjoint cycle))) = _
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  funext i
  change readMatrix (LinearMap.toMatrix'
    (natural ι cycle ∘ₗ (matrixOf v).toLin' ∘ₗ natural ι cycle⁻¹)) i = _
  rw [cycle_inv]
  have hc : natural ι cycle = (cycle.val.map ι).toLin' := rfl
  have hc2 : natural ι (cycle * cycle) = ((cycle * cycle).val.map ι).toLin' := rfl
  rw [hc, hc2]
  simp only [← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  fin_cases i <;>
    simp [readMatrix, matrixOf, cycle, Matrix.mul_apply,
      Matrix.map_apply, BinaryLinearThree.IrreducibleCatalogue.cycleMatrix,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem adjoint_shear (ι : F →+* K) :
    adjointMatrixEquiv (factorRep ι .adjoint shear) =
      BinaryLinearThree.IrreducibleCatalogue.shearMatrix.map (algebraMap (ZMod 2) K) := by
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix' (coordinates.conj
    (factorRep ι .adjoint shear))) = _
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  funext i
  change readMatrix (LinearMap.toMatrix'
    (natural ι shear ∘ₗ (matrixOf v).toLin' ∘ₗ natural ι shear⁻¹)) i = _
  rw [shear_inv]
  have hs : natural ι shear = (shear.val.map ι).toLin' := rfl
  rw [hs]
  simp only [← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  fin_cases i <;>
    simp [readMatrix, matrixOf, shear, Matrix.mul_apply,
      Matrix.map_apply, BinaryLinearThree.IrreducibleCatalogue.shearMatrix,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, CharTwo.add_self_eq_zero,
      add_assoc, add_comm, add_left_comm]
  ring

private theorem adjoint_density (ι : F →+* K) :
    Algebra.adjoin K (Set.range (factorRep ι .adjoint)) = ⊤ :=
  density_of_binary_generators (factorRep ι .adjoint) adjointMatrixEquiv
    cycle shear _ _ (adjoint_cycle ι) (adjoint_shear ι)
    BinaryLinearThree.IrreducibleCatalogue.Certificate.matrix_algebra_eq_top

omit [CharP F 2] [CharP K 2] in
private theorem dual_matrix (ι : F →+* K) (g : SL(3,F)) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin 3)).dualBasis ((natural ι).dual g) =
      (g⁻¹.val.map ι)ᵀ := by
  change LinearMap.toMatrix _ _ (Module.Dual.transpose (natural ι g⁻¹)) = _
  rw [LinearMap.toMatrix_transpose]
  change (LinearMap.toMatrix' (g⁻¹.val.map ι).toLin')ᵀ = _
  rw [LinearMap.toMatrix'_toLin']

omit [CharP F 2] in
private theorem dual_density (ι : F →+* K) :
    Algebra.adjoin K (Set.range (natural ι).dual) = ⊤ := by
  apply density_of_binary_generators (natural ι).dual
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin 3)).dualBasis)
    cycle.transpose⁻¹ shear.transpose⁻¹ BinaryLinearThree.IrreducibleCatalogue.cycle.val
    BinaryLinearThree.IrreducibleCatalogue.shear.val
  · rw [dual_matrix, inv_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycle, BinaryLinearThree.IrreducibleCatalogue.cycle, Matrix.map_apply,
        Matrix.SpecialLinearGroup.coe_transpose]
  · rw [dual_matrix, inv_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shear, BinaryLinearThree.IrreducibleCatalogue.shear, Matrix.map_apply,
        Matrix.SpecialLinearGroup.coe_transpose]
  · exact BinaryLinearThree.IrreducibleCatalogue.NaturalCertificate.matrix_algebra_eq_top

end TensorSimplicity

variable {F K : Type*} [Field F] [Field K] [CharP F 2] [CharP K 2]

/-- All four concrete restricted factors are simple over every characteristic-two
coefficient extension; neither finiteness nor algebraic closure is needed. -/
theorem factorRep_isIrreducible (ι : F →+* K) (a : Factor) :
    IsIrreducible (factorRep ι a) := by
  cases a with
  | trivial =>
    change IsIrreducible (Representation.trivial K SL(3,F) K)
    constructor
    intro S
    rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  | natural =>
    exact irreducible_of_jacobson_density_surjective (natural ι)
      (TensorSimplicity.natural_density ι)
  | dual =>
    exact irreducible_of_jacobson_density_surjective (natural ι).dual
      (TensorSimplicity.dual_density ι)
  | adjoint =>
    let : Nontrivial (Space K .adjoint) := Module.nontrivial_of_finrank_pos
      (show 0 < Module.finrank K (Space K .adjoint) by rw [finrank_space]; decide)
    exact irreducible_of_jacobson_density_surjective (factorRep ι .adjoint)
      (TensorSimplicity.adjoint_density ι)

namespace TensorSimplicity
/-- Remove the final trivial tensor factor in a one-letter word. -/
@[expose] def singletonEquiv (ι : F →+* K) (a : Factor) :
    (wordRep ι [a]).Equiv (factorRep ι a) :=
  Representation.TensorProduct.rid K (factorRep ι a)

/-- Simplicity of the one-letter words, including the field of two elements. -/
theorem singleton_isIrreducible (ι : F →+* K) (a : Factor) :
    IsIrreducible (wordRep ι [a]) :=
  (RepEquiv.irreducible_euqiv
    (RepEquiv.ofRepresentationEquiv (singletonEquiv ι a))).mpr (factorRep_isIrreducible ι a)

omit [CharP F 2] in
/-- One-letter word separation is the existing restricted-factor separation. -/
theorem singleton_equiv_imp_eq (ι : F →+* K) (a b : Factor)
    (e : (wordRep ι [a]).Equiv (wordRep ι [b])) : a = b :=
  factorRep_equiv_imp_eq ι a b
    (((singletonEquiv ι a).symm.trans e).trans (singletonEquiv ι b))
end TensorSimplicity
end Representation.SL3.BinaryDefiningFactors
