module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.Certificate

/-!
# Checked density certificate for M23 cocode factor 1

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, M23 paragraph, p.366.
Adapted from the project's M22 HermitianFiltration density certificates.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F1
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

private def c1 : List ℕ := [20, 2, 10, 6, 11, 448, 91, 704, 699, 539, 1627]

private def c2 : List ℕ := [763, 827, 766, 501, 54, 110, 333, 62, 1053, 329, 1301]

private def c3 : List ℕ := [347, 379, 325, 501, 451, 405, 760, 453, 1608, 754, 1269]

private def c4 : List ℕ := [1363, 1341, 1365, 1331, 1198, 1040, 407, 1387, 1252, 857, 1083]

private def c5 : List ℕ := [1190, 1331, 1198, 1341, 1365, 1616, 108, 1387, 1290, 226, 1920]

private def c6 : List ℕ := [1152, 144, 1397, 160, 118, 1319, 552, 30, 966, 550, 127]

private def c7 : List ℕ := [1323, 8, 24, 80, 208, 600, 210, 6, 1506, 226, 990]

private def c8 : List ℕ := [1328, 6, 13, 80, 656, 589, 658, 8, 1977, 857, 574]

private def c9 : List ℕ := [1329, 4, 9, 88, 640, 621, 722, 136, 1721, 345, 1598]

private def c10 : List ℕ := [1370, 11, 1389, 2, 449, 1190, 455, 80, 875, 386, 991]

private def c11 : List ℕ := [107, 15, 1380, 90, 833, 1739, 789, 216, 1490, 219, 1505]

private def c12 : List ℕ := [1491, 1382, 53, 6, 19, 112, 24, 2, 345, 1975, 385]

private def c13 : List ℕ := [219, 134, 133, 1387, 805, 1695, 795, 15, 1463, 186, 1377]

private def c14 : List ℕ := [176, 137, 1505, 1329, 100, 84, 14, 215, 101, 97, 128]

private def c15 : List ℕ := [100, 1507, 1413, 1363, 166, 123, 21, 1382, 1159, 1934, 1160]

private def c16 : List ℕ := [212, 1386, 100, 98, 194, 47, 27, 1457, 1250, 2031, 1032]

private def c17 : List ℕ := [210, 102, 178, 179, 590, 1833, 1965, 1363, 1805, 1677, 614]

private def c18 : List ℕ := [2, 1338, 54, 226, 664, 1948, 585, 1421, 2007, 1668, 725]

private def c19 : List ℕ := [214, 80, 82, 128, 602, 1971, 594, 60, 821, 363, 1757]

private def c20 : List ℕ := [214, 80, 82, 128, 327, 1198, 335, 60, 821, 363, 1757]

private def c21 : List ℕ := [0, 0, 0, 0, 797, 797, 797, 0, 0, 0, 0]

private def colsList : List ℕ := [112, 673, 1869, 2046, 162, 5, 695, 1834, 682, 997, 1573]

private def rowsOrbitList : List ℕ := [797, 179, 1170, 422, 1574, 435, 1527, 1467, 1964, 2043, 347]

private def ciList : List ℕ := [199, 126, 231, 443, 219, 1882, 1920, 1844, 1381, 171, 977]

private def riList : List ℕ := [1013, 1226, 587, 1385, 406, 1594, 2018, 145, 34, 1378, 1481]

private def cpList : List ℕ := [0, 0, 1, 3, 4, 5, 6, 7, 8, 9]

private def caList : List ℕ := [0, 1, 1, 0, 1, 1, 1, 0, 1, 1]

private def rpList : List ℕ := [0, 0, 1, 2, 3, 4, 5, 6, 7, 7]

private def raList : List ℕ := [0, 1, 1, 1, 0, 1, 1, 0, 0, 1]

private def at0 : List ℕ := [1872, 1886, 9, 1876, 1857, 256, 1248, 416, 32, 1920, 1024]

private def at1 : List ℕ := [1867, 183, 1532, 999, 1439, 191, 621, 13, 1610, 7, 1280]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 10) : Fin 11 := ⟨entry cpList x.val % 11, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 10) : Fin 11 := ⟨entry rpList x.val % 11, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 10) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 10) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 11) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 11), entry (transposed j) y.val = actionColumns j (blockIndex 1 y) >>> cut 1 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 11) (actors j) = factorMatrix 1 j := by
  have h : (matrix (n := 11) (transposed j)).transpose = factorMatrix 1 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 1 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 11, combineList c1 (entry c2 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 11, combineList c2 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 11, combineList c1 (entry c4 x.val) = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 11, combineList c2 (entry c5 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 11, combineList c2 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 11, combineList c1 (entry c7 x.val) = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 11, entry c0 x.val ^^^ entry c8 x.val = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 11, combineList c8 (entry c8 x.val) = entry c10 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check11 : ∀ x : Fin 11, entry c9 x.val ^^^ entry c10 x.val = entry c11 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check12 : ∀ x : Fin 11, combineList c8 (entry c10 x.val) = entry c12 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check13 : ∀ x : Fin 11, combineList c11 (entry c12 x.val) = entry c13 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check14 : ∀ x : Fin 11, entry c11 x.val ^^^ entry c13 x.val = entry c14 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check15 : ∀ x : Fin 11, combineList c12 (entry c12 x.val) = entry c15 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check16 : ∀ x : Fin 11, entry c14 x.val ^^^ entry c15 x.val = entry c16 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check17 : ∀ x : Fin 11, combineList c8 (entry c15 x.val) = entry c17 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check18 : ∀ x : Fin 11, combineList c16 (entry c17 x.val) = entry c18 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check19 : ∀ x : Fin 11, entry c16 x.val ^^^ entry c18 x.val = entry c19 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check20 : ∀ x : Fin 11, combineList c17 (entry c17 x.val) = entry c20 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check21 : ∀ x : Fin 11, entry c19 x.val ^^^ entry c20 x.val = entry c21 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cparent : ∀ x : Fin 10, cp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cstep : ∀ x : Fin 10, combineList (transposed (ca x)) (entry colsList (cp x).val) = entry colsList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cinverse : ∀ x : Fin 11, combineList colsList (entry ciList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rparent : ∀ x : Fin 10, rp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rstep : ∀ x : Fin 10, combineList (actors (ra x)) (entry rowsOrbitList (rp x).val) = entry rowsOrbitList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rinverse : ∀ x : Fin 11, combineList rowsOrbitList (entry riList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rankOne_checked : ∀ x : Fin 11, entry c21 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 11))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  have h3 := Certificate.mul_mem Q c2 c1 c3 h2 h1 (by decide +kernel) check3
  have h4 := Certificate.mul_mem Q c3 c2 c4 h3 h2 (by decide +kernel) check4
  have h5 := Certificate.mul_mem Q c4 c1 c5 h4 h1 (by decide +kernel) check5
  have h6 := Certificate.mul_mem Q c5 c2 c6 h5 h2 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c2 c7 h6 h2 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c1 c8 h7 h1 (by decide +kernel) check8
  have h9 := Certificate.add_mem Q c0 c8 c9 h0 h8 check9
  have h10 := Certificate.mul_mem Q c8 c8 c10 h8 h8 (by decide +kernel) check10
  have h11 := Certificate.add_mem Q c9 c10 c11 h9 h10 check11
  have h12 := Certificate.mul_mem Q c10 c8 c12 h10 h8 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c11 c13 h12 h11 (by decide +kernel) check13
  have h14 := Certificate.add_mem Q c11 c13 c14 h11 h13 check14
  have h15 := Certificate.mul_mem Q c12 c12 c15 h12 h12 (by decide +kernel) check15
  have h16 := Certificate.add_mem Q c14 c15 c16 h14 h15 check16
  have h17 := Certificate.mul_mem Q c15 c8 c17 h15 h8 (by decide +kernel) check17
  have h18 := Certificate.mul_mem Q c17 c16 c18 h17 h16 (by decide +kernel) check18
  have h19 := Certificate.add_mem Q c16 c18 c19 h16 h18 check19
  have h20 := Certificate.mul_mem Q c17 c17 c20 h17 h17 (by decide +kernel) check20
  have h21 := Certificate.add_mem Q c19 c20 c21 h19 h20 check21
  rw [← rankOne_eq c21 _ _ rankOne_checked]
  exact h21

/-- Density of the literal factor with flag index 1. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 1)) (Fin (degree 1)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 1 j ∈ Q) : Q = ⊤ := by
  have hA' : ∀ j : Fin 2, matrix (n := 11) (actors j) ∈ Q := by
    intro j
    rw [actors_checked]
    exact hA j
  apply full_of_orbits (m := 10) Q (fun j => matrix (n := 11) (actors j)) hA'
    colsList rowsOrbitList ciList riList cp rp ca ra cparent rparent
  · intro x
    have h := congrArg (vector (n := 11)) (cstep x)
    rw [vector_combine _ (show (transposed (ca x)).length = 11 from by
      generalize ca x = j; revert j; decide +kernel), transpose_checked,
      vecMul_transpose] at h
    exact h
  · intro x
    have h := congrArg (vector (n := 11)) (rstep x)
    rw [vector_combine _ (show (actors (ra x)).length = 11 from by
      generalize ra x = j; revert j; decide +kernel)] at h
    exact h
  · decide +kernel
  · decide +kernel
  · exact cinverse
  · exact rinverse
  · exact rankOne_mem Q hA'

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F1
