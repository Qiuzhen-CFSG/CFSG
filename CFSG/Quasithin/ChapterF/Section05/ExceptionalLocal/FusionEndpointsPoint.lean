module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphPointCard
public import Mathlib.LinearAlgebra.Matrix.Permutation
/-!
# The first endpoint graph centralizer is E₄ × S₄

The graph-fixed vector-local subgroup has order 48. We construct a faithful
C₂ × S₄ representation inside it: S₄ permutes the coordinates of the binary
alternating form with zero diagonal and all off-diagonal entries one; the
central C₂ is its all-one transvection. An explicit change of basis gives the
literal antidiagonal unitary form and fixes its first vector. The representation
is onto by the already proved order. Mapping binary entries into the unitary
field preserves the graph involution and the original matrix subgroup.

The small certificate checks only form preservation, the first column and
trivial kernel on 48 inputs; multiplication and determinant are structural.
Transport through the existing literal endpoint comparison identifies E₁.
Source: Aschbacher–Smith F.4.37(3) and F.5.3, printed pp.293,300.
-/

section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.EndpointPoint
open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "Mat" => Matrix (Fin 4) (Fin 4) (ZMod 2)
private def changeMatrix : Mat := !![1,0,0,1;1,1,1,0;1,1,0,0;1,0,1,0]
private def changeInverse : Mat := !![0,1,1,1;0,1,0,1;0,1,1,0;1,1,1,1]
private theorem change_inverse : changeMatrix * changeInverse = 1 := by decide +kernel
private theorem inverse_change : changeInverse * changeMatrix = 1 := by decide +kernel
private def centralMatrix (b : C2) : Mat := 1 + b.toAdd • (fun _ _ => 1)
private def centralHom : C2 →* Mat where
  toFun := centralMatrix
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private def binaryMatrix (a : C2 × S4) : Mat :=
  changeInverse * (centralHom a.1 * Matrix.permMatrixHom (R := ZMod 2) a.2) * changeMatrix
private theorem central_commutes : ∀ b : C2, ∀ p : S4,
    Commute (centralHom b) (Matrix.permMatrixHom (R := ZMod 2) p) := by
  change ∀ b : C2, ∀ p : S4, centralHom b * Matrix.permMatrixHom (R := ZMod 2) p =
    Matrix.permMatrixHom (R := ZMod 2) p * centralHom b
  decide +kernel
private def binaryHom : C2 × S4 →* Mat where
  toFun := binaryMatrix
  map_one' := by simp only [binaryMatrix, Prod.fst_one, Prod.snd_one, map_one, mul_one, inverse_change]
  map_mul' a b := by
    simp only [binaryMatrix, Prod.fst_mul, Prod.snd_mul, map_mul]
    have hc := (central_commutes b.1 a.2).eq
    calc
      _ = changeInverse * (centralHom a.1 *
          (centralHom b.1 * Matrix.permMatrixHom (R := ZMod 2) a.2) *
          Matrix.permMatrixHom (R := ZMod 2) b.2) * changeMatrix := by simp only [mul_assoc]
      _ = changeInverse * (centralHom a.1 *
          (Matrix.permMatrixHom (R := ZMod 2) a.2 * centralHom b.1) *
          Matrix.permMatrixHom (R := ZMod 2) b.2) * changeMatrix := by rw [hc]
      _ = _ := by
        have he := change_inverse
        calc
          _ = changeInverse * (centralHom a.1 * Matrix.permMatrixHom (R := ZMod 2) a.2) *
              (changeMatrix * changeInverse) *
              (centralHom b.1 * Matrix.permMatrixHom (R := ZMod 2) b.2) * changeMatrix := by rw [he]; simp only [mul_assoc, mul_one]
          _ = _ := by simp only [mul_assoc]
private theorem binary_valid : ∀ a : C2 × S4,
    (binaryMatrix a).transpose * gram (ZMod 2) * binaryMatrix a = gram (ZMod 2) ∧
    binaryMatrix a 0 0 = 1 ∧ binaryMatrix a 1 0 = 0 ∧
    binaryMatrix a 2 0 = 0 ∧ binaryMatrix a 3 0 = 0 := by
  decide +kernel
private theorem binary_det (a : C2 × S4) : (binaryMatrix a).det = 1 := by
  have hg : (gram (ZMod 2)).det = 1 := by decide +kernel
  have hd := congrArg Matrix.det (binary_valid a).1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg, mul_one] at hd
  apply CharTwo.sq_injective
  simpa only [pow_two, one_mul] using hd
private theorem binary_kernel : ∀ a : C2 × S4, binaryMatrix a = 1 → a = 1 := by
  decide +kernel

noncomputable section
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPointLocal
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
private def binaryCast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
private def liftedMatrix (a : C2 × S4) : Matrix (Fin 4) (Fin 4) F :=
  (binaryMatrix a).map binaryCast
private theorem cast_fixed (x : ZMod 2) : σ (binaryCast x) = binaryCast x :=
  DFunLike.congr_fun (Subsingleton.elim ((σ).toRingHom.comp binaryCast) binaryCast) x
private theorem gram_cast : (gram (ZMod 2)).map binaryCast = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram]
private theorem lifted_det (a : C2 × S4) : (liftedMatrix a).det = 1 := by
  change (binaryCast.mapMatrix (binaryMatrix a)).det = 1
  rw [← binaryCast.map_det, binary_det a, map_one]
private theorem lifted_unitary (a : C2 × S4) :
    (form F σ hσ).conjTranspose (liftedMatrix a) * gram F * liftedMatrix a = gram F := by
  have hf : (form F σ hσ).conjTranspose (liftedMatrix a) = (liftedMatrix a).transpose := by
    ext i j
    exact cast_fixed _
  rw [hf, liftedMatrix, ← Matrix.transpose_map, ← gram_cast,
    ← Matrix.map_mul, ← Matrix.map_mul, (binary_valid a).1]
private def pointSU (a : C2 × S4) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (liftedMatrix a)
    (by rw [lifted_det]; exact one_ne_zero),
    lifted_unitary a, Units.ext (lifted_det a)⟩
private theorem pointSU_local (a : C2 × S4) :
    pointSU a ∈ localSU F (form F σ hσ) := by
  apply (mem_localSU F _ _).mpr
  change binaryCast (binaryMatrix a 0 0) = 1 ∧
    binaryCast (binaryMatrix a 1 0) = 0 ∧
    binaryCast (binaryMatrix a 2 0) = 0 ∧
    binaryCast (binaryMatrix a 3 0) = 0
  rcases (binary_valid a).2 with ⟨h0,h1,h2,h3⟩
  simp only [h0,h1,h2,h3,map_one,map_zero,and_self]
private theorem pointSU_fixed (a : C2 × S4) :
    UnitaryFourOuter.matrixHom F σ hσ (pointSU a) = pointSU a := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact cast_fixed _
private def pointHom : C2 × S4 →* graphFixedLocal where
  toFun a := ⟨⟨pointSU a, pointSU_local a⟩, pointSU_fixed a⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom (a*b)) =
      binaryCast.mapMatrix (binaryHom a) * binaryCast.mapMatrix (binaryHom b)
    rw [map_mul, map_mul]
private theorem pointHom_injective : Function.Injective pointHom := by
  apply (injective_iff_map_eq_one pointHom).mpr
  intro a ha
  have hm : liftedMatrix a = 1 := congrArg (fun x : graphFixedLocal => x.val.val.val.val) ha
  apply binary_kernel a
  apply Matrix.map_injective binaryCast.injective
  change binaryCast.mapMatrix (binaryMatrix a) = binaryCast.mapMatrix 1
  rw [map_one]
  exact hm
private theorem pointHom_bijective : Function.Bijective pointHom := by
  apply pointHom_injective.bijective_of_nat_card_le
  rw [graphFixedLocal_card, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

public def graphFixedLocalEquivProduct : graphFixedLocal ≃* C2 × S4 :=
  (MulEquiv.ofBijective pointHom pointHom_bijective).symm

/-- The two canonical Klein-four generators retain their literal binary matrices. -/
public theorem graphFixedLocalEquivProduct_symm_klein_matrices :
    ((graphFixedLocalEquivProduct.symm
      (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)).val.val.val.val = !![1,1,1,1;0,1,0,1;0,0,1,1;0,0,0,1]) ∧
    ((graphFixedLocalEquivProduct.symm
      (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3)).val.val.val.val = !![1,1,0,1;0,1,0,0;0,0,1,1;0,0,0,1]) := by
  have h1 : binaryMatrix (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = !![1,1,1,1;0,1,0,1;0,0,1,1;0,0,0,1] := by decide +kernel
  have h2 : binaryMatrix (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) = !![1,1,0,1;0,1,0,0;0,0,1,1;0,0,0,1] := by decide +kernel
  constructor
  · change (binaryMatrix (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)).map binaryCast = _
    rw [h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · change (binaryMatrix (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3)).map binaryCast = _
    rw [h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.EndpointPoint

namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
private def reorderProduct : (C2 × S4) × C2 ≃* (C2 × C2) × S4 where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)
/-- The literal first endpoint's graph centralizer is E₄ × S₄. -/
public noncomputable def source_E_point_equiv (hi : Function.Injective i) :
    E c i false ≃* (C2 × C2) × S4 :=
  (source_E_point_equiv_fixedLocal c i hi).trans
    ((MulEquiv.prodCongr EndpointPoint.graphFixedLocalEquivProduct (MulEquiv.refl C2)).trans
      reorderProduct)
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
