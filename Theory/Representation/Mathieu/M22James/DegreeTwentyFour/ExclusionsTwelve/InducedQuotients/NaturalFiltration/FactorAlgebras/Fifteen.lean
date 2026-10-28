module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras.Arithmetic

/-!
# Checked density certificate in dimension 15

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
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate.Fifteen

private def actors : Fin 2 → Rows 15 :=
  ![![(8, 0), (16, 0), (32, 0), (4917, 20835), (23248, 370), (8066, 5382), (10104, 13914), (17659, 26684), (13717, 26217), (23097, 12884), (20384, 23853), (5306, 16929), (17877, 6687), (20954, 18757), (17957, 2269)],
    ![(19770, 16952), (1576, 28916), (14198, 17920), (3030, 29744), (30548, 17607), (17614, 13008), (3099, 17467), (31795, 3010), (14301, 12347), (18594, 32208), (14643, 30051), (2884, 15493), (10130, 12800), (10137, 13130), (1047, 16431)]]
private def transposedActors : Fin 2 → Rows 15 :=
  ![![(21384, 32008), (10400, 4216), (20744, 30368), (10945, 21952), (15322, 21200), (20172, 3480), (12496, 25432), (15792, 16384), (13672, 9272), (18040, 6976), (24032, 1376), (1584, 29824), (11064, 5736), (320, 960), (30352, 11656)],
    ![(26048, 19792), (22253, 26064), (18748, 18450), (8547, 24897), (30173, 875), (1671, 17739), (2364, 9906), (13096, 2738), (15645, 9856), (14622, 12453), (29175, 3676), (3785, 2688), (1428, 16170), (13716, 16170), (689, 18015)]]
private def columns : Rows 15 :=
  ![(24069, 23811), (16840, 4504), (7760, 19916), (4377, 14483), (21993, 947), (17906, 23465), (16971, 1994), (8750, 22040), (17029, 4462), (23430, 22349), (22464, 7080), (3369, 4137), (30797, 21499), (24656, 8653), (4779, 18010)]
private def columnInverse : Rows 15 :=
  ![(13591, 7175), (7744, 11109), (19122, 16117), (9141, 19683), (29350, 9393), (2660, 17269), (13605, 25354), (13272, 2216), (10818, 30983), (23427, 18215), (31715, 26849), (31970, 13937), (4421, 10772), (32707, 22549), (15585, 13411)]
private def rows : Rows 15 :=
  ![(3547, 32406), (23392, 9617), (20144, 31821), (23379, 2305), (25668, 25007), (25885, 18218), (8478, 13977), (10597, 3668), (29871, 19289), (10644, 30643), (11628, 18839), (21079, 10378), (11636, 479), (30165, 18386), (16417, 22795)]
private def rowInverse : Rows 15 :=
  ![(29327, 24613), (8474, 10569), (18258, 20323), (8635, 8213), (3640, 26022), (3842, 2965), (20286, 15596), (1424, 28891), (9221, 19594), (1605, 27559), (186, 6119), (11181, 17893), (18724, 1052), (21829, 5594), (15128, 25247)]
private def columnParent : Fin 14 → Fin 15 :=
  ![0, 0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 7, 8, 8]
private def columnActor : Fin 14 → Fin 2 :=
  ![0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1]
private def rowParent : Fin 14 → Fin 15 :=
  ![0, 0, 1, 1, 2, 3, 3, 4, 6, 6, 7, 8, 8, 9]
private def rowActor : Fin 14 → Fin 2 :=
  ![0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]
private def p1 : Rows 15 :=
  ![(4917, 20835), (23248, 370), (8066, 5382), (14580, 806), (12391, 11851), (5331, 10137), (23201, 1643), (31447, 23853), (11495, 29743), (19770, 16952), (1576, 28916), (14198, 17920), (16144, 5245), (1756, 8265), (64, 0)]
set_option maxRecDepth 100000 in
private theorem check_p1 : product (actors 0) (actors 0) = p1 := by
  decide +kernel
private def p2 : Rows 15 :=
  ![(14580, 806), (12391, 11851), (5331, 10137), (26495, 27212), (12265, 6030), (19270, 7326), (2884, 15493), (2560, 15044), (13366, 20195), (323, 330), (2235, 20050), (12733, 19580), (19990, 22052), (4515, 10989), (10104, 13914)]
set_option maxRecDepth 100000 in
private theorem check_p2 : product p1 (actors 0) = p2 := by
  decide +kernel
private def p3 : Rows 15 :=
  ![(13892, 257), (12545, 5957), (8192, 8192), (27082, 28117), (23317, 6285), (15182, 4515), (2048, 0), (2560, 3072), (0, 3584), (16, 48), (56, 24), (48, 56), (13956, 10698), (7326, 22488), (22595, 18228)]
set_option maxRecDepth 100000 in
private theorem check_p3 : product p2 (actors 1) = p3 := by
  decide +kernel
private def p4 : Rows 15 :=
  ![(4785, 3851), (5774, 3867), (9877, 1756), (3237, 7949), (7480, 165), (663, 11259), (14198, 17920), (19640, 914), (29900, 2216), (14773, 813), (12589, 12042), (11840, 8038), (23807, 23224), (7661, 4680), (16725, 691)]
set_option maxRecDepth 100000 in
private theorem check_p4 : product p3 p1 = p4 := by
  decide +kernel
private def p5 : Rows 15 :=
  ![(12114, 16128), (5774, 3867), (5790, 2868), (14019, 10697), (10078, 13921), (663, 11259), (4, 0), (5, 6), (0, 7), (1604, 12545), (12545, 10053), (10053, 9796), (8045, 7256), (6303, 20954), (0, 2560)]
set_option maxRecDepth 100000 in
private theorem check_p5 : product p4 (actors 1) = p5 := by
  decide +kernel
private def p6 : Rows 15 :=
  ![(21150, 21600), (3820, 164), (12247, 17371), (40, 48), (32, 40), (16, 16), (8066, 5382), (6339, 5443), (17687, 4976), (8009, 14023), (8890, 739), (14039, 11681), (7213, 10204), (15182, 4515), (1080, 32372)]
set_option maxRecDepth 100000 in
private theorem check_p6 : product p5 p1 = p6 := by
  decide +kernel
private def p7 : Rows 15 :=
  ![(28913, 21035), (29954, 15287), (3811, 1571), (0, 40), (48, 8), (8, 32), (12545, 5957), (1604, 4353), (1861, 13892), (2603, 5898), (20582, 5303), (758, 23026), (64, 320), (64, 128), (9673, 7578)]
set_option maxRecDepth 100000 in
private theorem check_p7 : product p6 p6 = p7 := by
  decide +kernel
private def p8 : Rows 15 := add identity p6
private def p9 : Rows 15 := add identity p7
private def p10 : Rows 15 :=
  ![(28497, 31424), (3579, 32414), (4551, 2445), (0, 0), (0, 0), (0, 0), (7196, 30491), (29549, 3539), (3579, 32414), (25258, 1118), (30523, 27407), (25218, 1150), (5529, 28537), (4559, 2469), (26356, 25258)]
set_option maxRecDepth 100000 in
private theorem check_p10 : product p8 p9 = p10 := by
  decide +kernel
private def p11 : Rows 15 :=
  ![(5946, 19895), (32334, 12667), (27511, 32586), (0, 0), (0, 0), (0, 0), (9671, 775), (515, 902), (32334, 12667), (26996, 31948), (13305, 27638), (5308, 19506), (6075, 27378), (9793, 642), (5560, 26996)]
set_option maxRecDepth 100000 in
private theorem check_p11 : product p10 (actors 1) = p11 := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem check_rankOne : product p11 p10 =
    rankOneRows (columns 0) (rows 0) := by
  decide +kernel

private lemma rankOne_mem (Q : Subalgebra Field (Mat 15))
    (hA : matrix (actors 0) ∈ Q) (hB : matrix (actors 1) ∈ Q) :
    vecMulVec (vector (columns 0)) (vector (rows 0)) ∈ Q := by
  have hI : matrix (identity : Rows 15) ∈ Q := by rw [matrix_identity]; exact Q.one_mem
  have h1 := matrix_mul_mem Q _ _ _ hA hA check_p1
  have h2 := matrix_mul_mem Q _ _ _ h1 hA check_p2
  have h3 := matrix_mul_mem Q _ _ _ h2 hB check_p3
  have h4 := matrix_mul_mem Q _ _ _ h3 h1 check_p4
  have h5 := matrix_mul_mem Q _ _ _ h4 hB check_p5
  have h6 := matrix_mul_mem Q _ _ _ h5 h1 check_p6
  have h7 := matrix_mul_mem Q _ _ _ h6 h6 check_p7
  have h8 := matrix_add_mem Q _ _ hI h6
  have h9 := matrix_add_mem Q _ _ hI h7
  have h10 := matrix_mul_mem Q _ _ _ h8 h9 check_p10
  have h11 := matrix_mul_mem Q _ _ _ h10 hB check_p11
  rw [← matrix_rankOneRows]
  exact matrix_mul_mem Q _ _ _ h11 h10 check_rankOne

set_option maxRecDepth 100000 in
private theorem actor_bits : ∀ (a : Fin 2) (i j : Fin 15),
    (actors a i).1.testBit j.val = (factorRows 0 a i).testBit (2*j.val) ∧
    (actors a i).2.testBit j.val = (factorRows 0 a i).testBit (2*j.val+1) := by
  decide +kernel

private lemma actors_eq (a : Fin 2) : matrix (actors a) = factorMatrix 0 a := by
  funext i j
  have h := actor_bits a i j
  simp only [matrix, vector, value, factorMatrix, digit, h.1, h.2]

set_option maxRecDepth 100000 in
private theorem transpose_bits : ∀ (a : Fin 2) (i j : Fin 15),
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

/-- The literal 15-dimensional factor generators span the full F₄ matrix algebra. -/
theorem density : FactorDensity 0 := by
  intro Q hA
  have hactors : ∀ a, matrix (actors a) ∈ Q := fun a => (actors_eq a).symm ▸ hA a
  apply full_of_orbits Q (fun a => matrix (actors a)) hactors columns rows
    columnInverse rowInverse columnParent rowParent columnActor rowActor
    column_parent_lt row_parent_lt
  · intro i
    have h := congrArg (vector (n := 15)) (column_step i)
    rw [vector_rowProduct, transpose_eq, vecMul_transpose] at h
    exact h
  · intro i
    exact (vector_rowProduct _ _).symm.trans (congrArg vector (row_step i))
  · exact column_inverse
  · exact row_inverse
  · exact rankOne_mem Q (hactors 0) (hactors 1)

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate.Fifteen
