module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.RankOne

/-!
# A cyclic matrix generates its centralizer

If the rows v C^i form a basis, a matrix commuting with C is a polynomial
in C: match its value on v by a linear combination of these rows, then use
commutation to match all basis vectors. The explicit one-sided inverse
certifies spanning, so no characteristic-polynomial or irreducibility oracle
is needed. This supplies the rank-one membership step for the ATLAS M24
binary degree-220 pairs; source data are attributed in ../source/README.md.
-/

open Matrix
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density

variable {F : Type*} [Field F] {n : ℕ}

theorem commuting_mem_of_cyclic_rows
    (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (C E X Xi : Matrix (Fin n) (Fin n) F) (v : Fin n → F)
    (hC : C ∈ S) (hCE : Commute C E)
    (hX : ∀ i : Fin n, X i = vecMul v (C ^ i.val))
    (hXi : Xi * X = 1) : E ∈ S := by
  classical
  let w := vecMul (vecMul v E) Xi
  let D : Matrix (Fin n) (Fin n) F := ∑ i : Fin n, w i • C ^ i.val
  have hD : D ∈ S := S.sum_mem fun i _ => S.smul_mem (S.pow_mem hC i.val) (w i)
  have hvD : vecMul v D = vecMul v E := by
    have he : vecMul v D = vecMul w X := by
      ext j
      simp only [D, vecMul, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [show X i j = vecMul v (C ^ i.val) j from congrFun (hX i) j]
      simp only [vecMul, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he]
    change vecMul (vecMul (vecMul v E) Xi) X = _
    rw [vecMul_vecMul, hXi, vecMul_one]
  have hCD : Commute C D := by
    change C * D = D * C
    simp only [D, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    rw [(Commute.refl C).pow_right i.val |>.eq]
  have hXD : X * D = X * E := by
    ext i j
    change vecMul (X i) D j = vecMul (X i) E j
    rw [hX i, vecMul_vecMul, (hCD.pow_left i.val).eq, ← vecMul_vecMul,
      hvD, vecMul_vecMul, ← (hCE.pow_left i.val).eq, ← vecMul_vecMul]
  have hDE : D = E := by
    calc
      D = (Xi * X) * D := by rw [hXi, one_mul]
      _ = (Xi * X) * E := by rw [mul_assoc, hXD, ← mul_assoc]
      _ = E := by rw [hXi, one_mul]
  rwa [hDE] at hD

/-- The preimage of a matrix subalgebra under transposition. -/
def transposePreimage (S : Subalgebra F (Matrix (Fin n) (Fin n) F)) :
    Subalgebra F (Matrix (Fin n) (Fin n) F) where
  carrier := {M | M.transpose ∈ S}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro A B ha hb; simpa using S.add_mem ha hb
  mul_mem' := by intro A B ha hb; simpa using S.mul_mem hb ha
  algebraMap_mem' := by
    intro r
    change ((algebraMap F (Matrix (Fin n) (Fin n) F)) r).transpose ∈ S
    rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose,
      ← Matrix.algebraMap_eq_diagonal]
    exact S.algebraMap_mem r

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
