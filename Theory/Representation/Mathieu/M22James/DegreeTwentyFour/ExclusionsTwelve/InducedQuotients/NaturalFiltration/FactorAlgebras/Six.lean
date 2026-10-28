module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras.Arithmetic

/-!
# Checked density certificate in dimension 6

The rank-one candidate and its two orbit bases are from the saved natural
induced Mathieu module calculation in `NaturalFiltration/source`.
All arithmetic identities below are checked by the kernel. Column orbit
vectors are stored as rows, so their inverse certificate is transposed.
The generators act on columns; the dual orbit multiplies on the right.
Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7. Original ATLAS attribution is preserved
in `NaturalFiltration/source/README.md`.
-/

@[expose] public section
open Matrix
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate.Six

private def actors : Fin 2 → Rows 6 :=
  ![![(14, 36), (20, 38), (38, 6), (35, 37), (6, 4), (33, 36)],
    ![(43, 14), (25, 7), (39, 54), (37, 18), (51, 54), (53, 35)]]
private def transposedActors : Fin 2 → Rows 6 :=
  ![![(40, 8), (29, 6), (23, 63), (1, 0), (2, 0), (44, 43)],
    ![(63, 34), (21, 63), (44, 23), (3, 1), (50, 28), (61, 52)]]
private def columns : Rows 6 :=
  ![(54, 38), (42, 24), (48, 46), (60, 30), (1, 36), (21, 3)]
private def columnInverse : Rows 6 :=
  ![(2, 46), (31, 39), (60, 25), (24, 38), (23, 35), (0, 11)]
private def rows : Rows 6 :=
  ![(13, 50), (59, 39), (62, 58), (21, 22), (10, 54), (56, 4)]
private def rowInverse : Rows 6 :=
  ![(9, 38), (32, 4), (34, 26), (26, 12), (32, 29), (0, 41)]
private def columnParent : Fin 5 → Fin 6 :=
  ![0, 1, 2, 3, 3]
private def columnActor : Fin 5 → Fin 2 :=
  ![1, 0, 0, 0, 1]
private def rowParent : Fin 5 → Fin 6 :=
  ![0, 1, 2, 3, 3]
private def rowActor : Fin 5 → Fin 2 :=
  ![1, 0, 0, 0, 1]
private def p1 : Rows 6 :=
  ![(51, 32), (36, 21), (51, 22), (61, 41), (52, 0), (13, 37)]
set_option maxRecDepth 100000 in
private theorem check_p1 : product (actors 0) (actors 0) = p1 := by
  decide +kernel
private def p2 : Rows 6 := add identity (actors 0)
private def p3 : Rows 6 := add identity p1
private def p4 : Rows 6 :=
  ![(37, 35), (19, 25), (8, 34), (31, 2), (35, 34), (1, 9)]
set_option maxRecDepth 100000 in
private theorem check_p4 : product p2 p3 = p4 := by
  decide +kernel
private def p5 : Rows 6 :=
  ![(11, 56), (8, 49), (45, 48), (40, 21), (10, 51), (46, 1)]
set_option maxRecDepth 100000 in
private theorem check_p5 : product p1 p1 = p5 := by
  decide +kernel
private def p6 : Rows 6 :=
  ![(12, 55), (34, 48), (18, 10), (61, 3), (27, 56), (27, 38)]
set_option maxRecDepth 100000 in
private theorem check_p6 : product p5 p5 = p6 := by
  decide +kernel
private def p7 : Rows 6 := add identity p5
private def p8 : Rows 6 :=
  ![(37, 15), (4, 20), (16, 33), (34, 36), (62, 60), (39, 63)]
set_option maxRecDepth 100000 in
private theorem check_p8 : product p4 p7 = p8 := by
  decide +kernel
private def p9 : Rows 6 := add identity (actors 0)
private def p10 : Rows 6 := add p9 p1
private def p11 : Rows 6 :=
  ![(37, 15), (59, 25), (47, 44), (34, 36), (51, 14), (24, 50)]
set_option maxRecDepth 100000 in
private theorem check_p11 : product p6 p10 = p11 := by
  decide +kernel
private def p12 : Rows 6 := add p8 p11
set_option maxRecDepth 100000 in
private theorem check_rankOne : product p12 identity =
    rankOneRows (columns 0) (rows 0) := by
  decide +kernel

private lemma rankOne_mem (Q : Subalgebra Field (Mat 6))
    (hA : matrix (actors 0) ∈ Q) (_hB : matrix (actors 1) ∈ Q) :
    vecMulVec (vector (columns 0)) (vector (rows 0)) ∈ Q := by
  have hI : matrix (identity : Rows 6) ∈ Q := by rw [matrix_identity]; exact Q.one_mem
  have h1 := matrix_mul_mem Q _ _ _ hA hA check_p1
  have h2 := matrix_add_mem Q _ _ hI hA
  have h3 := matrix_add_mem Q _ _ hI h1
  have h4 := matrix_mul_mem Q _ _ _ h2 h3 check_p4
  have h5 := matrix_mul_mem Q _ _ _ h1 h1 check_p5
  have h6 := matrix_mul_mem Q _ _ _ h5 h5 check_p6
  have h7 := matrix_add_mem Q _ _ hI h5
  have h8 := matrix_mul_mem Q _ _ _ h4 h7 check_p8
  have h9 := matrix_add_mem Q _ _ hI hA
  have h10 := matrix_add_mem Q _ _ h9 h1
  have h11 := matrix_mul_mem Q _ _ _ h6 h10 check_p11
  have h12 := matrix_add_mem Q _ _ h8 h11
  rw [← matrix_rankOneRows]
  exact matrix_mul_mem Q _ _ _ h12 hI check_rankOne

set_option maxRecDepth 100000 in
private theorem actor_bits : ∀ (a : Fin 2) (i j : Fin 6),
    (actors a i).1.testBit j.val = (factorRows 2 a i).testBit (2*j.val) ∧
    (actors a i).2.testBit j.val = (factorRows 2 a i).testBit (2*j.val+1) := by
  decide +kernel

private lemma actors_eq (a : Fin 2) : matrix (actors a) = factorMatrix 2 a := by
  funext i j
  have h := actor_bits a i j
  simp only [matrix, vector, value, factorMatrix, digit, h.1, h.2]

set_option maxRecDepth 100000 in
private theorem transpose_bits : ∀ (a : Fin 2) (i j : Fin 6),
    (transposedActors a i).1.testBit j.val = (actors a j).1.testBit i.val ∧
    (transposedActors a i).2.testBit j.val = (actors a j).2.testBit i.val := by
  decide +kernel

private lemma transpose_eq (a : Fin 2) :
    matrix (transposedActors a) = (matrix (actors a)).transpose := by
  funext i j
  have h := transpose_bits a i j
  simp only [matrix, vector, value, transpose_apply, h.1, h.2]

set_option maxRecDepth 100000 in
private theorem column_parent_lt : ∀ i, columnParent i < i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_parent_lt : ∀ i, rowParent i < i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem column_step : ∀ i,
    rowProduct (columns (columnParent i)) (transposedActors (columnActor i)) = columns i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_step : ∀ i,
    rowProduct (rows (rowParent i)) (actors (rowActor i)) = rows i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem column_inverse : product columnInverse columns = identity := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_inverse : product rowInverse rows = identity := by
  decide +kernel

/-- The literal 6-dimensional factor generators span the full F₄ matrix algebra. -/
theorem density : FactorDensity 2 := by
  intro Q hA
  have hactors : ∀ a, matrix (actors a) ∈ Q := fun a => (actors_eq a).symm ▸ hA a
  apply full_of_orbits Q (fun a => matrix (actors a)) hactors columns rows
    columnInverse rowInverse columnParent rowParent columnActor rowActor
    column_parent_lt row_parent_lt
  · intro i
    have h := congrArg (vector (n := 6)) (column_step i)
    rw [vector_rowProduct, transpose_eq, vecMul_transpose] at h
    exact h
  · intro i
    exact (vector_rowProduct _ _).symm.trans (congrArg vector (row_step i))
  · exact column_inverse
  · exact row_inverse
  · exact rankOne_mem Q (hactors 0) (hactors 1)

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate.Six
