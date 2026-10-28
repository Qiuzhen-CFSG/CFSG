module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# A determinant obstruction on a cyclic-four frame

Three vectors whose doubles are independent give an invertible frame modulo
two. An actor negating its first vector, fixing its second, and adding the
first to its third has determinant minus one. Thus it cannot have determinant
one over Z/4. The only finite checks concern binary triples and scalar
reduction, not matrix groups or automorphism groups.
-/

open Matrix
namespace ZModFourDeterminantObstruction
set_option backward.isDefEq.respectTransparency false
private abbrev Vec := Fin 3 → ZMod 4
private abbrev BinaryVec := Fin 3 → ZMod 2
private def reduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _

private theorem scalar_double : ∀ a b : ZMod 4,
    reduction a = reduction b ↔ a + a = b + b := by decide +kernel

private theorem reduce_eq (u v : Vec) :
    (fun i => reduction (u i)) = (fun i => reduction (v i)) ↔ u + u = v + v := by
  simp only [funext_iff, Pi.add_apply, scalar_double]

set_option synthInstance.maxSize 2048 in
private theorem binary_frame : ∀ u v p : Fin 3 → ZMod 2,
    u ≠ 0 → v ≠ 0 → u ≠ v → p ≠ 0 → p ≠ u → p ≠ v → p ≠ u + v →
      (Matrix.of ![u, v, p]).det ≠ 0 := by decide +kernel

/-- The indicated frame action contradicts determinant one when the
three doubled vectors are independent in the binary cube. -/
public theorem no_negated_fixed_shear
    (X : Matrix (Fin 3) (Fin 3) (ZMod 4)) (u v p : Fin 3 → ZMod 4)
    (hdet : X.det = 1) (hu : X.mulVec u = -u) (hv : X.mulVec v = v)
    (hp : X.mulVec p = p + u)
    (hu0 : u + u ≠ 0) (hv0 : v + v ≠ 0) (huv : u + u ≠ v + v)
    (hp0 : p + p ≠ 0) (hpu : p + p ≠ u + u) (hpv : p + p ≠ v + v)
    (hpuv : p + p ≠ (u + u) + (v + v)) : False := by
  let D : Matrix (Fin 3) (Fin 3) (ZMod 4) := (Matrix.of ![u, v, p]).transpose
  let R : Matrix (Fin 3) (Fin 3) (ZMod 4) := !![-1, 0, 1; 0, 1, 0; 0, 0, 1]
  have hXD : X * D = D * R := by
    ext i j
    fin_cases j
    · simpa [D, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun hu i
    · simpa [D, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun hv i
    · simpa [D, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        add_comm] using congrFun hp i
  have hdR : R.det = -1 := by decide +kernel
  have hh := congrArg Matrix.det hXD
  rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, hdR, mul_neg_one] at hh
  have hd0 : reduction D.det = 0 := by
    exact (by decide +kernel : ∀ a : ZMod 4, a = -a → reduction a = 0) D.det hh
  have hr0 (x : Vec) (hx : x + x ≠ 0) : (fun i => reduction (x i)) ≠ 0 := by
    intro he
    exact hx (by simpa only [Pi.zero_apply, map_zero, zero_add] using
      (reduce_eq x 0).mp he)
  have hne : (Matrix.of ![(fun i => reduction (u i)),
      (fun i => reduction (v i)), (fun i => reduction (p i))]).det ≠ 0 := by
    apply binary_frame _ _ _ (hr0 u hu0) (hr0 v hv0)
      (fun he => huv ((reduce_eq u v).mp he)) (hr0 p hp0)
      (fun he => hpu ((reduce_eq p u).mp he)) (fun he => hpv ((reduce_eq p v).mp he))
    intro he
    have he' : (fun i => reduction (p i)) = (fun i => reduction ((u + v) i)) := by
      exact he.trans (by ext i; simp only [Pi.add_apply, map_add])
    have hd := (reduce_eq p (u + v)).mp he'
    exact hpuv (hd.trans (by abel))
  apply hne
  rw [← Matrix.det_transpose]
  change (D.map reduction).det = 0
  exact (reduction.map_det D).symm.trans hd0

end ZModFourDeterminantObstruction
