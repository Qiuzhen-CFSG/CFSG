module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 12

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F12
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [565, 315, 918, 882, 297, 497, 55, 604, 166, 378]

private def c2 : List ℕ := [666, 458, 890, 930, 626, 51, 758, 655, 802, 275]

private def c3 : List ℕ := [902, 307, 238, 327, 110, 273, 411, 20, 968, 512]

private def c4 : List ℕ := [301, 880, 581, 9, 25, 954, 943, 703, 197, 378]

private def c5 : List ℕ := [339, 646, 517, 312, 842, 151, 773, 597, 409, 509]

private def c6 : List ℕ := [246, 300, 243, 705, 687, 215, 977, 119, 743, 856]

private def c7 : List ℕ := [136, 969, 360, 1008, 39, 545, 672, 157, 371, 279]

private def c8 : List ℕ := [302, 752, 530, 879, 361, 702, 727, 420, 839, 279]

private def c9 : List ℕ := [515, 811, 683, 892, 223, 207, 818, 740, 237, 378]

private def c10 : List ℕ := [628, 81, 683, 471, 168, 385, 63, 374, 331, 512]

private def c11 : List ℕ := [629, 83, 687, 479, 184, 417, 127, 502, 75, 0]

private def c12 : List ℕ := [445, 739, 261, 36, 288, 585, 112, 679, 646, 512]

private def c13 : List ℕ := [417, 526, 145, 782, 490, 981, 358, 222, 778, 0]

private def c14 : List ℕ := [980, 605, 574, 721, 338, 628, 281, 296, 833, 0]

private def c15 : List ℕ := [980, 448, 574, 844, 207, 1001, 793, 181, 833, 512]

private def c16 : List ℕ := [0, 925, 0, 413, 413, 413, 512, 413, 0, 512]

private def c17 : List ℕ := [0, 120, 0, 258, 258, 258, 378, 258, 0, 378]

private def c18 : List ℕ := [0, 925, 0, 925, 925, 925, 0, 925, 0, 0]

private def colsList : List ℕ := [186, 364, 611, 424, 755, 574, 790, 256, 727, 921]

private def rowsOrbitList : List ℕ := [925, 120, 142, 789, 899, 342, 419, 1006, 278, 921]

private def ciList : List ℕ := [813, 245, 743, 791, 124, 1015, 645, 104, 128, 686]

private def riList : List ℕ := [618, 524, 513, 229, 249, 318, 288, 236, 500, 366]

private def cpList : List ℕ := [0, 1, 2, 3, 3, 4, 5, 6, 6]

private def caList : List ℕ := [0, 1, 1, 0, 1, 1, 0, 0, 1]

private def rpList : List ℕ := [0, 0, 1, 2, 3, 3, 4, 5, 7]

private def raList : List ℕ := [0, 1, 1, 0, 0, 1, 1, 1, 0]

private def at0 : List ℕ := [115, 846, 453, 658, 751, 891, 680, 292, 574, 141]

private def at1 : List ℕ := [672, 1023, 192, 135, 629, 380, 86, 203, 782, 477]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns 1 j (blockIndex 1 2 y) >>> cut 1 2 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 1 2 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 1 2 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 1 2 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 10, combineList c2 (entry c2 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 10, combineList c1 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 10, combineList c2 (entry c4 x.val) = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 10, combineList c2 (entry c5 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 10, combineList c2 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 10, combineList c1 (entry c7 x.val) = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 10, combineList c2 (entry c8 x.val) = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 10, combineList c1 (entry c9 x.val) = entry c10 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check11 : ∀ x : Fin 10, entry c0 x.val ^^^ entry c10 x.val = entry c11 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check12 : ∀ x : Fin 10, combineList c10 (entry c10 x.val) = entry c12 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check13 : ∀ x : Fin 10, combineList c11 (entry c12 x.val) = entry c13 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check14 : ∀ x : Fin 10, entry c11 x.val ^^^ entry c13 x.val = entry c14 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check15 : ∀ x : Fin 10, combineList c12 (entry c12 x.val) = entry c15 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check16 : ∀ x : Fin 10, entry c14 x.val ^^^ entry c15 x.val = entry c16 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check17 : ∀ x : Fin 10, combineList c1 (entry c16 x.val) = entry c17 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check18 : ∀ x : Fin 10, combineList c16 (entry c17 x.val) = entry c18 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cparent : ∀ x : Fin 9, cp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cstep : ∀ x : Fin 9, combineList (transposed (ca x)) (entry colsList (cp x).val) = entry colsList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cinverse : ∀ x : Fin 10, combineList colsList (entry ciList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rparent : ∀ x : Fin 9, rp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rstep : ∀ x : Fin 9, combineList (actors (ra x)) (entry rowsOrbitList (rp x).val) = entry rowsOrbitList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rinverse : ∀ x : Fin 10, combineList rowsOrbitList (entry riList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rankOne_checked : ∀ x : Fin 10, entry c18 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 10))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  have h3 := Certificate.mul_mem Q c2 c2 c3 h2 h2 (by decide +kernel) check3
  have h4 := Certificate.mul_mem Q c3 c1 c4 h3 h1 (by decide +kernel) check4
  have h5 := Certificate.mul_mem Q c4 c2 c5 h4 h2 (by decide +kernel) check5
  have h6 := Certificate.mul_mem Q c5 c2 c6 h5 h2 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c2 c7 h6 h2 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c1 c8 h7 h1 (by decide +kernel) check8
  have h9 := Certificate.mul_mem Q c8 c2 c9 h8 h2 (by decide +kernel) check9
  have h10 := Certificate.mul_mem Q c9 c1 c10 h9 h1 (by decide +kernel) check10
  have h11 := Certificate.add_mem Q c0 c10 c11 h0 h10 check11
  have h12 := Certificate.mul_mem Q c10 c10 c12 h10 h10 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c11 c13 h12 h11 (by decide +kernel) check13
  have h14 := Certificate.add_mem Q c11 c13 c14 h11 h13 check14
  have h15 := Certificate.mul_mem Q c12 c12 c15 h12 h12 (by decide +kernel) check15
  have h16 := Certificate.add_mem Q c14 c15 c16 h14 h15 check16
  have h17 := Certificate.mul_mem Q c16 c1 c17 h16 h1 (by decide +kernel) check17
  have h18 := Certificate.mul_mem Q c17 c16 c18 h17 h16 (by decide +kernel) check18
  rw [← rankOne_eq c18 _ _ rankOne_checked]
  exact h18

/-- Density of the literal factor with orientation 1 and flag index 2. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 1 2)) (Fin (degree 1 2)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 1 2 j ∈ Q) : Q = ⊤ := by
  have hA' : ∀ j : Fin 2, matrix (n := 10) (actors j) ∈ Q := by
    intro j
    rw [actors_checked]
    exact hA j
  apply full_of_orbits Q (fun j => matrix (actors j)) hA'
    colsList rowsOrbitList ciList riList cp rp ca ra cparent rparent
  · intro x
    have h := congrArg (vector (n := 10)) (cstep x)
    rw [vector_combine _ (show (transposed (ca x)).length = 10 from by
      generalize ca x = j; revert j; decide +kernel), transpose_checked,
      vecMul_transpose] at h
    exact h
  · intro x
    have h := congrArg (vector (n := 10)) (rstep x)
    rw [vector_combine _ (show (actors (ra x)).length = 10 from by
      generalize ra x = j; revert j; decide +kernel)] at h
    exact h
  · decide +kernel
  · decide +kernel
  · exact cinverse
  · exact rinverse
  · exact rankOne_mem Q hA'

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F12
