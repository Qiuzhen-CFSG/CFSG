module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Two-factor coordinates for the K.3.4 tensor descent

Evaluation at two distinct support positions identifies the coordinate index
with a pair of natural-module indices. The tensor-product basis then gives a
linear equivalence. Its pure-tensor formula identifies the product-of-matrix-
entries action with the tensor product of the two graph-twisted natural actions.

Source: GLS3, Examples 2.8.10(d); Aschbacher--Smith K.3.4, printed p.456.
-/

public section

open Representation
open scoped TensorProduct
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
noncomputable section
variable {F K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field K]

private def pairIndex {n : ℕ} (j k : Fin (2*n)) (hjk : j ≠ k) :
    (({j,k} : Finset (Fin (2*n))) → Coordinate) ≃ Coordinate × Coordinate where
  toFun x := (x ⟨j, by simp⟩, x ⟨k, by simp⟩)
  invFun x t := if t.val = j then x.1 else x.2
  left_inv x := by
    funext t
    rcases t with ⟨t, ht⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [hjk.symm]
  right_inv x := by simp [hjk.symm]

private def pairCoordinates {n : ℕ} (j k : Fin (2*n)) (hjk : j ≠ k) :
    ((Coordinate → K) ⊗[K] (Coordinate → K)) ≃ₗ[K]
      ((({j,k} : Finset (Fin (2*n))) → Coordinate) → K) :=
  ((Pi.basisFun K Coordinate).tensorProduct (Pi.basisFun K Coordinate)).equivFun.trans
    (LinearEquiv.funCongrLeft K K (pairIndex j k hjk))

private theorem pairCoordinates_tmul {n : ℕ} (j k : Fin (2*n)) (hjk : j ≠ k)
    (v w : Coordinate → K) (x : ({j,k} : Finset (Fin (2*n))) → Coordinate) :
    pairCoordinates j k hjk (v ⊗ₜ[K] w) x =
      v (x ⟨j, by simp⟩) * w (x ⟨k, by simp⟩) := by
  simp [pairCoordinates, LinearEquiv.funCongrLeft, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, pairIndex]
  exact mul_comm _ _

/-- The two selected coordinate factors form the genuine tensor product of their actions. -/
def tensorModel_pair_equiv {n : ℕ} (e : F →+* K)
    (j k : Fin (2*n)) (hjk : j ≠ k) :
    (tensorModel e {j,k}).Equiv
      ((mapCoefficients e (basicTwist F j)).tprod (mapCoefficients e (basicTwist F k))) := by
  apply Representation.Equiv.symm
  refine .mk (pairCoordinates j k hjk) ?_
  intro g
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  funext x
  change pairCoordinates j k hjk
    (mapCoefficients e (basicTwist F j) g v ⊗ₜ[K]
      mapCoefficients e (basicTwist F k) g w) x =
      (tensorMatrix e {j,k} g).mulVec (pairCoordinates j k hjk (v ⊗ₜ[K] w)) x
  rw [pairCoordinates_tmul]
  have hb (l : Fin (2*n)) (z : Coordinate → K) (i : Coordinate) :
      mapCoefficients e (basicTwist F l) g z i =
        ∑ t, e (((graphDerived F ^ (l : ℕ)) g).val.val i t) * z t := by
    change ((LinearMap.toMatrix' (basicTwist F l g)).map e).mulVec z i = _
    have hm : LinearMap.toMatrix' (basicTwist F l g) =
        ((graphDerived F ^ (l : ℕ)) g).val.val := LinearMap.toMatrix'_toLin' _
    rw [hm]
    rfl
  rw [hb, hb]
  simp only [Matrix.mulVec, dotProduct, pairCoordinates_tmul]
  have hm (y : ({j,k} : Finset (Fin (2*n))) → Coordinate) :
      tensorMatrix e {j,k} g x y =
        e (((graphDerived F ^ (j : ℕ)) g).val.val (x ⟨j, by simp⟩) (y ⟨j, by simp⟩)) *
        e (((graphDerived F ^ (k : ℕ)) g).val.val (x ⟨k, by simp⟩) (y ⟨k, by simp⟩)) := by
    apply Finset.prod_eq_mul (⟨j, by simp⟩ : ({j,k} : Finset (Fin (2*n))))
      (⟨k, by simp⟩ : ({j,k} : Finset (Fin (2*n))))
      (by intro h; exact hjk (congrArg Subtype.val h))
    · intro t _ ⟨htj, htk⟩
      have ht := t.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ht | ht
      · exact (htj (Subtype.ext ht)).elim
      · exact (htk (Subtype.ext ht)).elim
    · simp
    · simp
  simp_rw [hm]
  rw [← (pairIndex j k hjk).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pairIndex, Equiv.coe_fn_symm_mk,
    if_true, if_neg hjk.symm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
