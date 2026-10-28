module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.Certificate

/-!
# Checked density certificate for M23 cocode factor 3

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, M23 paragraph, p.366.
Adapted from the project's M22 HermitianFiltration density certificates.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F3
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

private def c1 : List ℕ := [564, 520, 764, 384, 727, 424, 261, 128, 136, 386, 1266]

private def c2 : List ℕ := [302, 174, 1513, 1327, 1402, 1284, 137, 1390, 1389, 1899, 194]

private def c3 : List ℕ := [764, 580, 564, 3, 927, 40, 426, 1390, 65, 173, 1525]

private def c4 : List ℕ := [4, 635, 1, 60, 29, 40, 552, 1443, 817, 96, 1608]

private def c5 : List ℕ := [1513, 819, 302, 184, 1170, 43, 1856, 1093, 854, 1421, 527]

private def c6 : List ℕ := [333, 1016, 1, 63, 120, 427, 589, 1164, 690, 297, 1581]

private def c7 : List ℕ := [197, 624, 564, 63, 1018, 28, 463, 1806, 117, 660, 1424]

private def c8 : List ℕ := [288, 1948, 764, 312, 542, 1468, 460, 684, 1072, 662, 1467]

private def c9 : List ℕ := [288, 1235, 4, 631, 545, 1273, 625, 982, 1933, 801, 1593]

private def c10 : List ℕ := [105, 479, 1513, 1013, 833, 346, 1714, 2012, 1602, 1580, 982]

private def c11 : List ℕ := [104, 477, 1517, 1021, 849, 378, 1778, 1884, 1858, 1068, 2006]

private def c12 : List ℕ := [1140, 967, 1596, 1691, 1717, 411, 482, 1931, 663, 700, 1655]

private def c13 : List ℕ := [1762, 1688, 1985, 1471, 776, 263, 1611, 428, 1145, 1867, 891]

private def c14 : List ℕ := [1674, 1861, 556, 1602, 89, 125, 185, 1776, 827, 871, 1197]

private def c15 : List ℕ := [1671, 1997, 834, 1245, 1574, 641, 1698, 255, 525, 702, 904]

private def c16 : List ℕ := [13, 136, 366, 671, 1663, 764, 1563, 1551, 310, 473, 1829]

private def c17 : List ℕ := [1657, 1187, 1795, 1932, 150, 409, 675, 1247, 89, 1064, 1095]

private def c18 : List ℕ := [1782, 851, 1871, 564, 406, 980, 1455, 570, 758, 1862, 213]

private def c19 : List ℕ := [1787, 987, 1569, 171, 2025, 296, 948, 1077, 960, 1695, 2032]

private def c20 : List ℕ := [566, 987, 748, 1126, 2025, 1509, 948, 248, 960, 594, 829]

private def c21 : List ℕ := [1229, 0, 1229, 1229, 0, 1229, 0, 1229, 0, 1229, 1229]

private def colsList : List ℕ := [1709, 1885, 1213, 687, 634, 773, 858, 893, 1912, 1182, 202]

private def rowsOrbitList : List ℕ := [1229, 1087, 506, 1397, 1736, 415, 1889, 1639, 1821, 1613, 1622]

private def ciList : List ℕ := [655, 450, 708, 1254, 375, 329, 1144, 1372, 281, 370, 459]

private def riList : List ℕ := [1290, 1892, 1694, 317, 1363, 1241, 1897, 388, 314, 901, 1093]

private def cpList : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 7, 9]

private def caList : List ℕ := [1, 1, 0, 1, 0, 1, 1, 0, 1, 0]

private def rpList : List ℕ := [0, 1, 2, 3, 3, 4, 6, 7, 7, 8]

private def raList : List ℕ := [0, 1, 1, 0, 1, 1, 1, 0, 1, 1]

private def at0 : List ℕ := [80, 1552, 85, 294, 1045, 1061, 1044, 1980, 616, 23, 1024]

private def at1 : List ℕ := [844, 1691, 427, 991, 16, 927, 1940, 1094, 957, 512, 956]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 10) : Fin 11 := ⟨entry cpList x.val % 11, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 10) : Fin 11 := ⟨entry rpList x.val % 11, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 10) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 10) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 11) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 11), entry (transposed j) y.val = actionColumns j (blockIndex 3 y) >>> cut 3 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 11) (actors j) = factorMatrix 3 j := by
  have h : (matrix (n := 11) (transposed j)).transpose = factorMatrix 3 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 3 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 11, combineList c2 (entry c1 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 11, combineList c1 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 11, combineList c2 (entry c4 x.val) = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 11, combineList c2 (entry c5 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 11, combineList c1 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 11, combineList c2 (entry c7 x.val) = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 11, combineList c1 (entry c8 x.val) = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 11, combineList c2 (entry c9 x.val) = entry c10 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check11 : ∀ x : Fin 11, entry c0 x.val ^^^ entry c10 x.val = entry c11 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check12 : ∀ x : Fin 11, combineList c10 (entry c10 x.val) = entry c12 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check13 : ∀ x : Fin 11, combineList c11 (entry c12 x.val) = entry c13 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check14 : ∀ x : Fin 11, entry c11 x.val ^^^ entry c13 x.val = entry c14 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check15 : ∀ x : Fin 11, combineList c12 (entry c12 x.val) = entry c15 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check16 : ∀ x : Fin 11, entry c14 x.val ^^^ entry c15 x.val = entry c16 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check17 : ∀ x : Fin 11, combineList c10 (entry c15 x.val) = entry c17 x.val := by decide +kernel

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
  have h3 := Certificate.mul_mem Q c1 c2 c3 h1 h2 (by decide +kernel) check3
  have h4 := Certificate.mul_mem Q c3 c1 c4 h3 h1 (by decide +kernel) check4
  have h5 := Certificate.mul_mem Q c4 c2 c5 h4 h2 (by decide +kernel) check5
  have h6 := Certificate.mul_mem Q c5 c2 c6 h5 h2 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c1 c7 h6 h1 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c2 c8 h7 h2 (by decide +kernel) check8
  have h9 := Certificate.mul_mem Q c8 c1 c9 h8 h1 (by decide +kernel) check9
  have h10 := Certificate.mul_mem Q c9 c2 c10 h9 h2 (by decide +kernel) check10
  have h11 := Certificate.add_mem Q c0 c10 c11 h0 h10 check11
  have h12 := Certificate.mul_mem Q c10 c10 c12 h10 h10 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c11 c13 h12 h11 (by decide +kernel) check13
  have h14 := Certificate.add_mem Q c11 c13 c14 h11 h13 check14
  have h15 := Certificate.mul_mem Q c12 c12 c15 h12 h12 (by decide +kernel) check15
  have h16 := Certificate.add_mem Q c14 c15 c16 h14 h15 check16
  have h17 := Certificate.mul_mem Q c15 c10 c17 h15 h10 (by decide +kernel) check17
  have h18 := Certificate.mul_mem Q c17 c16 c18 h17 h16 (by decide +kernel) check18
  have h19 := Certificate.add_mem Q c16 c18 c19 h16 h18 check19
  have h20 := Certificate.mul_mem Q c17 c17 c20 h17 h17 (by decide +kernel) check20
  have h21 := Certificate.add_mem Q c19 c20 c21 h19 h20 check21
  rw [← rankOne_eq c21 _ _ rankOne_checked]
  exact h21

/-- Density of the literal factor with flag index 3. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 3)) (Fin (degree 3)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 3 j ∈ Q) : Q = ⊤ := by
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

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F3
