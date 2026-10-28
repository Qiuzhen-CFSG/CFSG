module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity.Certificate
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Data.Matrix.Basic

/-!
# Density of the augmentation actor matrices over characteristic two

A rank-one matrix with spanning left and right word orbits generates all
matrix units after the two checked changes of basis. Hence every subalgebra
containing the two binary actors is the full matrix algebra. Restriction of
scalars pulls an arbitrary characteristic-two subalgebra back to the binary
one, and the images of the binary matrix units span the whole target algebra.

The finite identities are proved in Certificate. This supplies the absolute
simplicity argument for the geometric degree-twelve module in
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2, pp.9--10.
-/

@[expose] public section

open scoped BigOperators Matrix
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
set_option backward.isDefEq.respectTransparency false

private lemma dense_of_rank_one {K : Type*} [CommSemiring K]
    (Q : Subalgebra K (Matrix (Fin 12) (Fin 12) K))
    (C D C' D' : Matrix (Fin 12) (Fin 12) K)
    (hC : C * C' = 1) (hD : D' * D = 1)
    (hunit : ∀ i j, Matrix.vecMulVec (fun k => C k i) (D j) ∈ Q) : Q = ⊤ := by
  have hs (i j : Fin 12) : C * Matrix.single i j 1 * D ∈ Q := by
    have he : C * Matrix.single i j 1 * D =
        Matrix.vecMulVec (fun k => C k i) (D j) := by
      rw [Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
        Matrix.vecMulVec_mul, Matrix.mulVec_single_one, Matrix.single_one_vecMul]
      rfl
    rw [he]
    exact hunit i j
  have hm (M : Matrix (Fin 12) (Fin 12) K) : C * M * D ∈ Q := by
    rw [Matrix.matrix_eq_sum_single M, Matrix.mul_sum, Matrix.sum_mul]
    apply Q.sum_mem
    intro i _
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Q.sum_mem
    intro j _
    have he : C * Matrix.single i j (M i j) * D =
        (M i j) • (C * Matrix.single i j 1 * D) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single]
      simp only [smul_eq_mul, mul_one]
    rw [he]
    exact Q.smul_mem (hs i j) _
  apply top_unique
  intro M _
  have h := hm (C' * M * D')
  have he : C * (C' * M * D') * D = M := by
    calc
      C * (C' * M * D') * D = (C * C') * M * (D' * D) := by simp only [mul_assoc]
      _ = M := by rw [hC, hD, one_mul, mul_one]
  rwa [he] at h

attribute [local irreducible] A M C D Cinv Dinv c r
  w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11

set_option backward.isDefEq.respectTransparency true in
lemma binary_dense (Q : Subalgebra (ZMod 2) Mat) (h : ∀ a, A a ∈ Q) : Q = ⊤ := by
  have hw0 : w0 ∈ Q := by rw [w0_eq]; exact Q.one_mem
  have hw1 : w1 ∈ Q := by rw [w1_eq]; exact Q.mul_mem (h 0) hw0
  have hw2 : w2 ∈ Q := by rw [w2_eq]; exact Q.mul_mem (h 1) hw0
  have hw3 : w3 ∈ Q := by rw [w3_eq]; exact Q.mul_mem (h 0) hw1
  have hw4 : w4 ∈ Q := by rw [w4_eq]; exact Q.mul_mem (h 0) hw2
  have hw5 : w5 ∈ Q := by rw [w5_eq]; exact Q.mul_mem (h 1) hw1
  have hw6 : w6 ∈ Q := by rw [w6_eq]; exact Q.mul_mem (h 1) hw2
  have hw7 : w7 ∈ Q := by rw [w7_eq]; exact Q.mul_mem (h 0) hw4
  have hw8 : w8 ∈ Q := by rw [w8_eq]; exact Q.mul_mem (h 0) hw5
  have hw9 : w9 ∈ Q := by rw [w9_eq]; exact Q.mul_mem (h 0) hw6
  have hw10 : w10 ∈ Q := by rw [w10_eq]; exact Q.mul_mem (h 1) hw3
  have hw11 : w11 ∈ Q := by rw [w11_eq]; exact Q.mul_mem (h 1) hw4
  have hw12 : w12 ∈ Q := by rw [w12_eq]; exact Q.mul_mem (h 1) hw5
  have hw13 : w13 ∈ Q := by rw [w13_eq]; exact Q.mul_mem (h 0) hw10
  have hw14 : w14 ∈ Q := by rw [w14_eq]; exact Q.mul_mem (h 1) hw7
  have hw15 : w15 ∈ Q := by rw [w15_eq]; exact Q.mul_mem (h 1) hw9
  have hw16 : w16 ∈ Q := by rw [w16_eq]; exact Q.mul_mem (h 1) hw10
  have hw17 : w17 ∈ Q := by rw [w17_eq]; exact Q.mul_mem (h 1) hw11
  have hM : M ∈ Q := by rw [M_eq]; exact Q.add_mem hw17 hw2
  have hp0 : p0 ∈ Q := by rw [p0_eq]; exact Q.one_mem
  have hp1 : p1 ∈ Q := by rw [p1_eq]; exact Q.mul_mem hp0 hM
  have hp2 : p2 ∈ Q := by rw [p2_eq]; exact Q.add_mem (Q.mul_mem hp1 hM) Q.one_mem
  have hp3 : p3 ∈ Q := by rw [p3_eq]; exact Q.add_mem (Q.mul_mem hp2 hM) Q.one_mem
  have hp4 : p4 ∈ Q := by rw [p4_eq]; exact Q.add_mem (Q.mul_mem hp3 hM) Q.one_mem
  have hp5 : p5 ∈ Q := by rw [p5_eq]; exact Q.add_mem (Q.mul_mem hp4 hM) Q.one_mem
  have hp6 : p6 ∈ Q := by rw [p6_eq]; exact Q.add_mem (Q.mul_mem hp5 hM) Q.one_mem
  have hp7 : p7 ∈ Q := by rw [p7_eq]; exact Q.add_mem (Q.mul_mem hp6 hM) Q.one_mem
  have hp8 : p8 ∈ Q := by rw [p8_eq]; exact Q.add_mem (Q.mul_mem hp7 hM) Q.one_mem
  have hp9 : p9 ∈ Q := by rw [p9_eq]; exact Q.mul_mem hp8 hM
  have hp10 : p10 ∈ Q := by rw [p10_eq]; exact Q.mul_mem hp9 hM
  have hp11 : p11 ∈ Q := by rw [p11_eq]; exact Q.add_mem (Q.mul_mem hp10 hM) Q.one_mem
  have hl : ∀ i, leftWords i ∈ Q := by
    intro i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
    · exact hw3
    · exact hw5
    · exact hw4
    · exact hw10
    · exact hw12
    · exact hw7
    · exact hw13
    · exact hw16
    · exact hw14
  have hr : ∀ i, rightWords i ∈ Q := by
    intro i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
    · exact hw4
    · exact hw5
    · exact hw6
    · exact hw8
    · exact hw9
    · exact hw10
    · exact hw11
    · exact hw14
    · exact hw15
  refine dense_of_rank_one Q C D Cinv Dinv C_inverse D_inverse ?_
  intro i j
  have he : Matrix.vecMulVec (fun k => C k i) (D j) = leftWords i * p11 * rightWords j := by
    rw [rank_one, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    · funext k; exact congrFun (congrFun columns k) i
    · funext k; exact congrFun (congrFun rows j) k
  exact he.symm ▸ Q.mul_mem (Q.mul_mem (hl i) hp11) (hr j)

variable (F : Type*) [Field F] [CharP F 2]
def castMatrix : Mat →+* Matrix (Fin 12) (Fin 12) F :=
  (ZMod.castHom (dvd_refl 2) F).mapMatrix
lemma field_dense (Q : Subalgebra F (Matrix (Fin 12) (Fin 12) F))
    (h : ∀ a, castMatrix F (A a) ∈ Q) : Q = ⊤ := by
  let : Algebra (ZMod 2) F := (ZMod.castHom (dvd_refl 2) F).toAlgebra
  let φ : Mat →ₐ[ZMod 2] Matrix (Fin 12) (Fin 12) F :=
    (Algebra.ofId (ZMod 2) F).mapMatrix
  have hb : (Q.restrictScalars (ZMod 2)).comap φ = ⊤ := binary_dense _ h
  have hs (i j : Fin 12) : Matrix.single i j (1 : F) ∈ Q := by
    have hm : Matrix.single i j (1 : ZMod 2) ∈ (Q.restrictScalars (ZMod 2)).comap φ := by
      rw [hb]; trivial
    change φ (Matrix.single i j 1) ∈ Q at hm
    have he : φ (Matrix.single i j 1) = Matrix.single i j 1 := by
      ext k l
      change (ZMod.castHom (dvd_refl 2) F) (Matrix.single i j 1 k l) = _
      simp only [Matrix.single_apply]
      split <;> simp
    rwa [he] at hm
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  exact Q.sum_mem (fun i _ => Q.sum_mem (fun j _ => by
    simpa using Q.smul_mem (hs i j) (M i j)))

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
