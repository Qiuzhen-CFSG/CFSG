module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 05

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F05
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [912, 672, 900, 192, 897, 258, 136, 128, 640, 384]

private def c2 : List ℕ := [74, 745, 491, 138, 110, 357, 610, 327, 481, 246]

private def c3 : List ℕ := [1, 630, 392, 804, 143, 839, 280, 203, 1003, 300]

private def c4 : List ℕ := [912, 687, 704, 390, 756, 316, 449, 504, 1018, 198]

private def c5 : List ℕ := [62, 790, 979, 932, 819, 395, 654, 837, 346, 39]

private def c6 : List ℕ := [643, 635, 255, 222, 703, 655, 569, 724, 398, 557]

private def c7 : List ℕ := [48, 635, 255, 621, 503, 884, 83, 397, 996, 86]

private def c8 : List ℕ := [267, 438, 492, 730, 135, 917, 175, 397, 700, 270]

private def c9 : List ℕ := [968, 687, 704, 478, 527, 415, 992, 397, 475, 617]

private def c10 : List ℕ := [696, 790, 979, 290, 820, 778, 855, 397, 131, 817]

private def c11 : List ℕ := [835, 421, 441, 290, 519, 352, 701, 724, 432, 531]

private def c12 : List ℕ := [470, 98, 365, 621, 958, 742, 401, 598, 429, 571]

private def c13 : List ℕ := [424, 494, 973, 730, 723, 436, 130, 504, 232, 980]

private def c14 : List ℕ := [329, 41, 793, 478, 286, 70, 942, 837, 714, 951]

private def c15 : List ℕ := [328, 43, 797, 470, 270, 102, 1006, 965, 970, 439]

private def c16 : List ℕ := [499, 209, 244, 465, 314, 158, 144, 131, 683, 281]

private def c17 : List ℕ := [1002, 109, 606, 935, 863, 43, 715, 678, 673, 602]

private def c18 : List ℕ := [674, 70, 323, 625, 593, 77, 293, 355, 363, 1005]

private def c19 : List ℕ := [574, 218, 323, 625, 527, 77, 441, 417, 503, 947]

private def c20 : List ℕ := [156, 156, 0, 0, 94, 0, 156, 194, 156, 94]

private def c21 : List ℕ := [72, 72, 0, 0, 388, 0, 72, 460, 72, 388]

private def c22 : List ℕ := [744, 744, 0, 0, 333, 0, 744, 933, 744, 333]

private def c23 : List ℕ := [74, 74, 0, 0, 732, 0, 74, 662, 74, 732]

private def c24 : List ℕ := [0, 0, 0, 0, 94, 0, 0, 94, 0, 94]

private def c25 : List ℕ := [156, 156, 0, 0, 0, 0, 156, 156, 156, 0]

private def colsList : List ℕ := [451, 466, 550, 384, 305, 857, 490, 682, 372, 424]

private def rowsOrbitList : List ℕ := [156, 69, 72, 963, 744, 568, 74, 375, 1, 448]

private def ciList : List ℕ := [585, 910, 663, 227, 586, 747, 462, 752, 760, 1014]

private def riList : List ℕ := [256, 68, 53, 307, 169, 758, 311, 430, 665, 844]

private def cpList : List ℕ := [0, 0, 1, 2, 2, 3, 3, 4, 5]

private def caList : List ℕ := [0, 1, 1, 0, 1, 0, 1, 1, 1]

private def rpList : List ℕ := [0, 0, 1, 2, 3, 4, 5, 6, 7]

private def raList : List ℕ := [0, 1, 1, 1, 0, 0, 1, 1, 1]

private def at0 : List ℕ := [16, 32, 4, 64, 1, 2, 8, 991, 565, 279]

private def at1 : List ℕ := [422, 733, 688, 31, 512, 886, 1015, 782, 420, 66]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns 0 j (blockIndex 0 5 y) >>> cut 0 5 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 0 5 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 0 5 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 0 5 j x y
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
private theorem check7 : ∀ x : Fin 10, combineList c1 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 10, combineList c2 (entry c7 x.val) = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 10, combineList c2 (entry c8 x.val) = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 10, combineList c2 (entry c9 x.val) = entry c10 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check11 : ∀ x : Fin 10, combineList c1 (entry c10 x.val) = entry c11 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check12 : ∀ x : Fin 10, combineList c2 (entry c11 x.val) = entry c12 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check13 : ∀ x : Fin 10, combineList c2 (entry c12 x.val) = entry c13 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check14 : ∀ x : Fin 10, combineList c2 (entry c13 x.val) = entry c14 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check15 : ∀ x : Fin 10, entry c0 x.val ^^^ entry c14 x.val = entry c15 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check16 : ∀ x : Fin 10, combineList c14 (entry c14 x.val) = entry c16 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check17 : ∀ x : Fin 10, combineList c15 (entry c16 x.val) = entry c17 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check18 : ∀ x : Fin 10, entry c15 x.val ^^^ entry c17 x.val = entry c18 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check19 : ∀ x : Fin 10, combineList c16 (entry c16 x.val) = entry c19 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check20 : ∀ x : Fin 10, entry c18 x.val ^^^ entry c19 x.val = entry c20 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check21 : ∀ x : Fin 10, combineList c2 (entry c20 x.val) = entry c21 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check22 : ∀ x : Fin 10, combineList c2 (entry c21 x.val) = entry c22 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check23 : ∀ x : Fin 10, combineList c1 (entry c22 x.val) = entry c23 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check24 : ∀ x : Fin 10, combineList c20 (entry c23 x.val) = entry c24 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check25 : ∀ x : Fin 10, entry c24 x.val ^^^ entry c20 x.val = entry c25 x.val := by decide +kernel

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
private theorem rankOne_checked : ∀ x : Fin 10, entry c25 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

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
  have h7 := Certificate.mul_mem Q c6 c1 c7 h6 h1 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c2 c8 h7 h2 (by decide +kernel) check8
  have h9 := Certificate.mul_mem Q c8 c2 c9 h8 h2 (by decide +kernel) check9
  have h10 := Certificate.mul_mem Q c9 c2 c10 h9 h2 (by decide +kernel) check10
  have h11 := Certificate.mul_mem Q c10 c1 c11 h10 h1 (by decide +kernel) check11
  have h12 := Certificate.mul_mem Q c11 c2 c12 h11 h2 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c2 c13 h12 h2 (by decide +kernel) check13
  have h14 := Certificate.mul_mem Q c13 c2 c14 h13 h2 (by decide +kernel) check14
  have h15 := Certificate.add_mem Q c0 c14 c15 h0 h14 check15
  have h16 := Certificate.mul_mem Q c14 c14 c16 h14 h14 (by decide +kernel) check16
  have h17 := Certificate.mul_mem Q c16 c15 c17 h16 h15 (by decide +kernel) check17
  have h18 := Certificate.add_mem Q c15 c17 c18 h15 h17 check18
  have h19 := Certificate.mul_mem Q c16 c16 c19 h16 h16 (by decide +kernel) check19
  have h20 := Certificate.add_mem Q c18 c19 c20 h18 h19 check20
  have h21 := Certificate.mul_mem Q c20 c2 c21 h20 h2 (by decide +kernel) check21
  have h22 := Certificate.mul_mem Q c21 c2 c22 h21 h2 (by decide +kernel) check22
  have h23 := Certificate.mul_mem Q c22 c1 c23 h22 h1 (by decide +kernel) check23
  have h24 := Certificate.mul_mem Q c23 c20 c24 h23 h20 (by decide +kernel) check24
  have h25 := Certificate.add_mem Q c24 c20 c25 h24 h20 check25
  rw [← rankOne_eq c25 _ _ rankOne_checked]
  exact h25

/-- Density of the literal factor with orientation 0 and flag index 5. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 0 5)) (Fin (degree 0 5)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 0 5 j ∈ Q) : Q = ⊤ := by
  have hA' : ∀ j : Fin 2, matrix (n := 10) (actors j) ∈ Q := by
    intro j
    rw [actors_checked]
    exact hA j
  apply full_of_orbits (m := 9) Q (fun j => matrix (n := 10) (actors j)) hA'
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

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F05
