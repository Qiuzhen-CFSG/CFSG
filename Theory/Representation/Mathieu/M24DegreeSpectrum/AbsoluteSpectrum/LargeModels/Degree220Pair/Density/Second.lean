module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.ChecksSecond
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.RankOne

/-!
# Full matrix algebra for the second degree-220 pair

The short algebra expression C has a checked cyclic basis. Its two null
vectors supply a rank-one matrix in the generated algebra. Both generator
orbits of its factors span, by the checked inverse identities, so their
outer products span all matrices. Transposition matches the published
column-action convention exactly. No group-realization input is used.
Sources: James (1973), J. Algebra 27, 57–111, and the ATLAS files attributed
in Degree220Pair/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
open Matrix Packed Witnesses.Second

private theorem second_a : (decodePacked 220 a).transpose = matrixA true := by
  rw [rows_sound 220 a secondRowsA ChecksSecond.a_rows]
  rfl

private theorem second_b : (decodePacked 220 b).transpose = matrixB true := by
  rw [rows_sound 220 b secondRowsB ChecksSecond.b_rows]
  rfl

theorem second_full : Algebra.adjoin (ZMod 2)
    ({matrixA true, matrixB true} : Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) = ⊤ := by
  let S : Subalgebra (ZMod 2) (Matrix (Fin 220) (Fin 220) (ZMod 2)) :=
    Algebra.adjoin (ZMod 2)
    ({matrixA true, matrixB true} : Set (Matrix (Fin 220) (Fin 220) (ZMod 2)))
  have ha : (decodePacked 220 a).transpose ∈ S := by
    rw [second_a]
    exact Algebra.subset_adjoin (by simp)
  have hb : (decodePacked 220 b).transpose ∈ S := by
    rw [second_b]
    exact Algebra.subset_adjoin (by simp)
  let R : Subalgebra (ZMod 2) (Matrix (Fin 220) (Fin 220) (ZMod 2)) :=
    transposePreimage (F := ZMod 2) (n := 220) S
  have har : decodePacked 220 a ∈ R := ha
  have hbr : decodePacked 220 b ∈ R := hb
  have hbs : decodePacked 220 bs ∈ R := by
    rw [← mul_sound 220 b b bs ChecksSecond.bs_mul]
    exact R.mul_mem hbr hbr
  have hab : decodePacked 220 ab ∈ R := by
    rw [← mul_sound 220 a bs ab ChecksSecond.ab_mul]
    exact R.mul_mem har hbs
  have hab2 : decodePacked 220 ab2 ∈ R := by
    rw [← mul_sound 220 ab ab ab2 ChecksSecond.ab2_mul]
    exact R.mul_mem hab hab
  have hab3 : decodePacked 220 ab3 ∈ R := by
    rw [← mul_sound 220 ab2 ab ab3 ChecksSecond.ab3_mul]
    exact R.mul_mem hab2 hab
  have hword : decodePacked 220 word ∈ R := by
    rw [← mul_sound 220 ab3 a word ChecksSecond.word_mul]
    exact R.mul_mem hab3 har
  have hsum : decodePacked 220 sumAB ∈ R := by
    rw [← add_sound 220 a bs sumAB ChecksSecond.sum_add]
    exact R.add_mem har hbs
  have hc : decodePacked 220 c ∈ R := by
    rw [← add_sound 220 sumAB word c ChecksSecond.c_add]
    exact R.add_mem hsum hword
  have hv : (decodePacked 220 c).mulVec (vector 220 v) = 0 := by
    rw [← vecMul_transpose,
      ← transpose_sound 220 cT c ChecksSecond.c_transpose,
      ← vector_row, ChecksSecond.v_kernel]
    ext i
    simp [vector, Thompson.BinaryMatrix.bit]
  have hl : vecMul (vector 220 lam) (decodePacked 220 c) = 0 := by
    rw [← vector_row, ChecksSecond.lam_kernel]
    ext i
    simp [vector, Thompson.BinaryMatrix.bit]
  have he : vecMulVec (vector 220 v) (vector 220 lam) ∈ R :=
    rankOne_mem_of_cyclic_rows R (decodePacked 220 c) (decodePacked 220 x)
      (decodePacked 220 xi) (vector 220 v) (vector 220 lam) (vector 220 seed)
      hc hv hl (cyclic_sound 220 c x seed ChecksSecond.x_cyclic)
      (inverse_sound 220 xi x ChecksSecond.x_inverse)
  have he' : vecMulVec (vector 220 lam) (vector 220 v) ∈ S := by
    change (vecMulVec (vector 220 v) (vector 220 lam)).transpose ∈ S at he
    rwa [transpose_vecMulVec] at he
  have haT : decodePacked 220 aT ∈ S := by
    rw [transpose_sound 220 aT a ChecksSecond.a_transpose]
    exact ha
  have hbT : decodePacked 220 bT ∈ S := by
    rw [transpose_sound 220 bT b ChecksSecond.b_transpose]
    exact hb
  exact Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.top_of_rankOne
    S (vector 220 lam) (vector 220 v) (decodePacked 220 p) (decodePacked 220 pi)
    (decodePacked 220 q) (decodePacked 220 qi) he'
    (column_reachable 220 a b l p lam parentsL lettersL
      (transpose_sound 220 l p ChecksSecond.l_transpose)
      ChecksSecond.left_orbit S ha hb)
    (row_reachable 220 aT bT q v parentsR lettersR ChecksSecond.right_orbit S haT hbT)
    (inverse_sound 220 p pi ChecksSecond.p_inverse)
    (inverse_sound 220 qi q ChecksSecond.q_inverse)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
