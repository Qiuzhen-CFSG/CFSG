module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 01

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F01
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [607, 1015, 4, 598, 516, 759, 491, 128, 34, 20]

private def c2 : List ℕ := [249, 96, 237, 131, 165, 30, 600, 167, 792, 581]

private def c3 : List ℕ := [574, 582, 630, 62, 173, 171, 59, 205, 379, 9]

private def c4 : List ℕ := [322, 524, 767, 342, 634, 393, 781, 358, 708, 9]

private def c5 : List ℕ := [288, 555, 246, 360, 69, 965, 458, 467, 87, 122]

private def c6 : List ℕ := [725, 285, 619, 360, 944, 774, 232, 741, 579, 185]

private def c7 : List ℕ := [11, 810, 25, 477, 321, 464, 610, 176, 132, 102]

private def c8 : List ℕ := [26, 416, 223, 469, 441, 322, 99, 28, 74, 715]

private def c9 : List ℕ := [933, 597, 149, 278, 88, 574, 692, 86, 74, 641]

private def c10 : List ℕ := [496, 172, 22, 816, 638, 752, 692, 624, 699, 539]

private def c11 : List ℕ := [497, 174, 18, 824, 622, 720, 756, 752, 955, 27]

private def c12 : List ℕ := [753, 934, 708, 46, 939, 593, 243, 33, 649, 521]

private def c13 : List ℕ := [336, 828, 13, 340, 487, 368, 485, 801, 34, 722]

private def c14 : List ℕ := [161, 914, 31, 620, 905, 928, 785, 465, 921, 713]

private def c15 : List ℕ := [464, 914, 31, 797, 905, 928, 127, 160, 247, 214]

private def c16 : List ℕ := [369, 0, 0, 369, 0, 0, 878, 369, 878, 543]

private def c17 : List ℕ := [258, 0, 0, 258, 0, 0, 789, 258, 789, 535]

private def c18 : List ℕ := [878, 0, 0, 878, 0, 0, 0, 878, 0, 878]

private def colsList : List ℕ := [649, 251, 37, 124, 830, 190, 348, 207, 503, 1023]

private def rowsOrbitList : List ℕ := [878, 655, 789, 533, 105, 492, 75, 572, 578, 693]

private def ciList : List ℕ := [213, 749, 486, 411, 83, 311, 273, 980, 383, 667]

private def riList : List ℕ := [671, 993, 794, 422, 1012, 945, 152, 441, 12, 633]

private def cpList : List ℕ := [0, 0, 1, 2, 2, 3, 4, 6, 7]

private def caList : List ℕ := [0, 1, 1, 0, 1, 0, 1, 1, 0]

private def rpList : List ℕ := [0, 0, 1, 2, 2, 3, 4, 6, 7]

private def raList : List ℕ := [0, 1, 1, 0, 1, 0, 1, 1, 0]

private def at0 : List ℕ := [99, 363, 575, 65, 555, 354, 107, 226, 66, 59]

private def at1 : List ℕ := [669, 168, 692, 357, 353, 151, 583, 157, 256, 832]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns 0 j (blockIndex 0 1 y) >>> cut 0 1 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 0 1 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 0 1 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 0 1 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 10, combineList c2 (entry c2 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 10, combineList c1 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 10, combineList c2 (entry c4 x.val) = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 10, combineList c1 (entry c5 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 10, combineList c2 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 10, combineList c2 (entry c7 x.val) = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 10, combineList c1 (entry c8 x.val) = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 10, combineList c2 (entry c9 x.val) = entry c10 x.val := by decide +kernel

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
private theorem check17 : ∀ x : Fin 10, combineList c2 (entry c16 x.val) = entry c17 x.val := by decide +kernel

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
  have h6 := Certificate.mul_mem Q c5 c1 c6 h5 h1 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c2 c7 h6 h2 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c2 c8 h7 h2 (by decide +kernel) check8
  have h9 := Certificate.mul_mem Q c8 c1 c9 h8 h1 (by decide +kernel) check9
  have h10 := Certificate.mul_mem Q c9 c2 c10 h9 h2 (by decide +kernel) check10
  have h11 := Certificate.add_mem Q c0 c10 c11 h0 h10 check11
  have h12 := Certificate.mul_mem Q c10 c10 c12 h10 h10 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c11 c13 h12 h11 (by decide +kernel) check13
  have h14 := Certificate.add_mem Q c11 c13 c14 h11 h13 check14
  have h15 := Certificate.mul_mem Q c12 c12 c15 h12 h12 (by decide +kernel) check15
  have h16 := Certificate.add_mem Q c14 c15 c16 h14 h15 check16
  have h17 := Certificate.mul_mem Q c16 c2 c17 h16 h2 (by decide +kernel) check17
  have h18 := Certificate.mul_mem Q c17 c16 c18 h17 h16 (by decide +kernel) check18
  rw [← rankOne_eq c18 _ _ rankOne_checked]
  exact h18

/-- Density of the literal factor with orientation 0 and flag index 1. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 0 1)) (Fin (degree 0 1)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 0 1 j ∈ Q) : Q = ⊤ := by
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

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F01
