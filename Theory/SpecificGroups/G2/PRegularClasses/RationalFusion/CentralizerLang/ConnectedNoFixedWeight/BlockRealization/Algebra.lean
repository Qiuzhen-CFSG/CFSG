module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.Peirce
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockModel
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Realizing the determinant-one Peirce action on split octonions

An SL₃ matrix acts on coordinates 0, 5, 6 and its cofactor matrix acts on
coordinates 7, 2, 1, while the two diagonal idempotents are fixed. The
multiplication table becomes the usual dot and cross product formulas.
Cofactor covariance of cross products and preservation of the pairing
prove that this is an actual octonion automorphism, in every characteristic.
The faithful Peirce restriction identifies its diagonal subgroup with the
published G₂ torus, so block centralizers map into the actual centralizer.

This supplies the algebraic realization used for Steinberg 8.5 and 12.5
(`refs/KGroup/GLS3/Chapter2St2.tex`). The literal octonion multiplication is
from the licensed ATLAS port (`LICENSES/ATLAS.txt`).
-/

@[expose] public section

open Matrix Atlas.SplitOctonion
open scoped MatrixGroups
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
section
variable {K : Type*} [CommRing K]

def cofactor (A : Matrix (Fin 3) (Fin 3) K) := A.adjugate.transpose

theorem cofactor_cross (A : Matrix (Fin 3) (Fin 3) K) (u v : Fin 3 → K) :
    crossProduct (A *ᵥ u) (A *ᵥ v) = cofactor A *ᵥ crossProduct u v := by
  ext i
  fin_cases i <;> simp [cross_apply, cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem cofactor_cofactor (A : SL(3,K)) : cofactor (cofactor A.val) = A.val := by
  simp [cofactor, Matrix.adjugate_transpose, Matrix.adjugate_adjugate, A.property]

def pack (a b : K) (u v : Fin 3 → K) : Carrier K :=
  ![u 0,v 2,v 1,a,b,u 1,u 2,v 0]

theorem pack_mul (a b c d : K) (u v w z : Fin 3 → K) :
    mul (pack a b u v) (pack c d w z) =
    pack (a*c - u ⬝ᵥ z) (b*d - v ⬝ᵥ w)
      (a • w + d • u + crossProduct v z)
      (b • z + c • v + crossProduct u w) := by
  ext i
  fin_cases i <;> simp [mul, pack, cross_apply, dotProduct, Fin.sum_univ_three] <;> ring


def blockLinear (A : Matrix (Fin 3) (Fin 3) K) : Carrier K →ₗ[K] Carrier K where
  toFun x := pack (x 3) (x 4) (A *ᵥ ![x 0,x 5,x 6])
    (cofactor A *ᵥ ![x 7,x 2,x 1])
  map_add' x y := by
    ext i
    fin_cases i <;> simp [pack, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [pack, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem blockLinear_pack (A : Matrix (Fin 3) (Fin 3) K) (a b : K) (u v : Fin 3 → K) :
    blockLinear A (pack a b u v) = pack a b (A *ᵥ u) (cofactor A *ᵥ v) := by
  simp [blockLinear, pack, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

omit [CommRing K] in
theorem pack_eta (x : Carrier K) :
    pack (x 3) (x 4) ![x 0,x 5,x 6] ![x 7,x 2,x 1] = x := by
  ext i; fin_cases i <;> rfl

theorem blockLinear_mul (A B : Matrix (Fin 3) (Fin 3) K) (x : Carrier K) :
    blockLinear (A*B) x = blockLinear A (blockLinear B x) := by
  conv_rhs => rw [← pack_eta x]
  rw [blockLinear_pack, blockLinear_pack, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp [blockLinear, cofactor, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

theorem blockLinear_one (x : Carrier K) : blockLinear (1 : Matrix (Fin 3) (Fin 3) K) x = x := by
  simpa [blockLinear, cofactor] using pack_eta x

theorem cofactor_dot (A : SL(3,K)) (u v : Fin 3 → K) :
    (A.val *ᵥ u) ⬝ᵥ (cofactor A.val *ᵥ v) = u ⬝ᵥ v := by
  rw [cofactor, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, A.property, one_smul, Matrix.one_mulVec, dotProduct_comm]

theorem block_preserves_mul (A : SL(3,K)) (x y : Carrier K) :
    blockLinear A.val (mul x y) = mul (blockLinear A.val x) (blockLinear A.val y) := by
  obtain ⟨a,b,u,v,hx⟩ : ∃ a b u v, x = pack a b u v :=
    ⟨x 3,x 4,![x 0,x 5,x 6],![x 7,x 2,x 1],(pack_eta x).symm⟩
  obtain ⟨c,d,w,z,hy⟩ : ∃ c d w z, y = pack c d w z :=
    ⟨y 3,y 4,![y 0,y 5,y 6],![y 7,y 2,y 1],(pack_eta y).symm⟩
  rw [hx,hy,pack_mul,blockLinear_pack,blockLinear_pack,blockLinear_pack,pack_mul]
  rw [cofactor_dot, dotProduct_comm (cofactor A.val *ᵥ v),cofactor_dot, dotProduct_comm w v,
    cofactor_cross, cofactor_cross, cofactor_cofactor]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

noncomputable def blockEquiv (A : SL(3,K)) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := blockLinear A.val
  invFun := blockLinear A⁻¹.val
  left_inv x := by
    change blockLinear (A⁻¹).val (blockLinear A.val x) = x
    rw [← blockLinear_mul]
    have h : (A⁻¹).val * A.val = 1 := congrArg Subtype.val (inv_mul_cancel A)
    rw [h,blockLinear_one]
  right_inv x := by
    change blockLinear A.val (blockLinear (A⁻¹).val x) = x
    rw [← blockLinear_mul]
    have h : A.val * (A⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel A)
    rw [h,blockLinear_one]

end
section
variable {K : Type*} [Field K]
noncomputable def blockHom : SL(3,K) →* Model K where
  toFun A := ⟨blockEquiv A,block_preserves_mul A⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_one
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_mul A.val B.val

theorem blockHom_fixes_three (A : SL(3,K)) :
    (blockHom A).val (basisVector 3) = basisVector 3 := by
  ext i; fin_cases i <;> simp [blockHom,blockEquiv,blockLinear,pack,basisVector,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem blockHom_fixes_four (A : SL(3,K)) :
    (blockHom A).val (basisVector 4) = basisVector 4 := by
  ext i; fin_cases i <;> simp [blockHom,blockEquiv,blockLinear,pack,basisVector,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem peirceMatrix_blockHom (A : SL(3,K)) : peirceMatrix (blockHom A) = A.val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceMatrix,peirceIndex,blockHom,blockEquiv,blockLinear,pack,basisVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem blockHom_diagonal (l m : Kˣ) :
    blockHom (diagonalSL (peirceWeights l m) (peirceWeights_prod l m)) = torus l m := by
  apply peirceMatrix_injective_on_fixers
    _ _ (blockHom_fixes_three _) (blockHom_fixes_four _)
  · ext i; fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]
  · ext i; fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]
  · rw [peirceMatrix_blockHom]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalSL,peirceWeights,peirceMatrix,peirceIndex,torus,torusEquiv,
        torusLinear,torusWeights,basisVector]

theorem blockHom_centralizes (l m : Kˣ)
    (A : Subgroup.centralizer ({diagonalSL (peirceWeights l m) (peirceWeights_prod l m)} :
      Set (SL(3,K)))) :
    blockHom A.val ∈ Subgroup.centralizer ({torus l m} : Set (Model K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← blockHom_diagonal, ← map_mul, ← map_mul]
  exact congrArg blockHom (Subgroup.mem_centralizer_singleton_iff.mp A.property)

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
