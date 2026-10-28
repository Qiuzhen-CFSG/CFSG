module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 17

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F17
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [516, 2, 36, 40, 244, 32, 64, 160, 332, 37]

private def c2 : List ℕ := [1, 767, 306, 574, 428, 824, 147, 642, 702, 887]

private def c3 : List ℕ := [581, 767, 522, 262, 439, 824, 147, 442, 289, 523]

private def c4 : List ℕ := [727, 512, 950, 371, 356, 355, 464, 617, 391, 951]

private def c5 : List ℕ := [726, 514, 946, 379, 372, 323, 400, 745, 135, 439]

private def c6 : List ℕ := [523, 951, 488, 135, 642, 483, 858, 160, 143, 831]

private def c7 : List ℕ := [24, 136, 966, 399, 348, 617, 685, 938, 244, 794]

private def c8 : List ℕ := [718, 650, 116, 244, 40, 810, 829, 323, 115, 685]

private def c9 : List ℕ := [516, 37, 529, 244, 40, 810, 344, 323, 115, 2]

private def c10 : List ℕ := [202, 687, 613, 0, 0, 0, 613, 0, 0, 687]

private def c11 : List ℕ := [720, 831, 495, 0, 0, 0, 495, 0, 0, 831]

private def c12 : List ℕ := [49, 951, 902, 0, 0, 0, 902, 0, 0, 951]

private def c13 : List ℕ := [661, 531, 134, 0, 0, 0, 134, 0, 0, 531]

private def c14 : List ℕ := [593, 727, 134, 0, 0, 0, 134, 0, 0, 727]

private def c15 : List ℕ := [585, 774, 335, 0, 0, 0, 335, 0, 0, 774]

private def c16 : List ℕ := [0, 613, 613, 0, 0, 0, 613, 0, 0, 613]

private def colsList : List ℕ := [582, 380, 225, 685, 560, 293, 1018, 234, 630, 300]

private def rowsOrbitList : List ℕ := [613, 495, 902, 134, 335, 774, 991, 516, 887, 1]

private def ciList : List ℕ := [137, 676, 121, 681, 463, 206, 973, 910, 30, 273]

private def riList : List ℕ := [512, 377, 341, 338, 417, 54, 695, 36, 473, 469]

private def cpList : List ℕ := [0, 1, 2, 3, 3, 4, 6, 7, 8]

private def caList : List ℕ := [1, 0, 1, 0, 1, 1, 1, 0, 1]

private def rpList : List ℕ := [0, 1, 2, 3, 4, 4, 5, 6, 7]

private def raList : List ℕ := [1, 0, 1, 1, 0, 1, 1, 0, 0]

private def at0 : List ℕ := [512, 2, 789, 264, 16, 700, 336, 144, 256, 1]

private def at1 : List ℕ := [579, 974, 794, 314, 878, 830, 514, 466, 564, 938]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns 1 j (blockIndex 1 7 y) >>> cut 1 7 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 1 7 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 1 7 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 1 7 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 10, combineList c2 (entry c1 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 10, combineList c2 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 10, entry c0 x.val ^^^ entry c4 x.val = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 10, combineList c4 (entry c4 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 10, combineList c5 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 10, entry c5 x.val ^^^ entry c7 x.val = entry c8 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check9 : ∀ x : Fin 10, combineList c6 (entry c6 x.val) = entry c9 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check10 : ∀ x : Fin 10, entry c8 x.val ^^^ entry c9 x.val = entry c10 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check11 : ∀ x : Fin 10, combineList c2 (entry c10 x.val) = entry c11 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check12 : ∀ x : Fin 10, combineList c1 (entry c11 x.val) = entry c12 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check13 : ∀ x : Fin 10, combineList c2 (entry c12 x.val) = entry c13 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check14 : ∀ x : Fin 10, combineList c1 (entry c13 x.val) = entry c14 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check15 : ∀ x : Fin 10, combineList c2 (entry c14 x.val) = entry c15 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check16 : ∀ x : Fin 10, combineList c10 (entry c15 x.val) = entry c16 x.val := by decide +kernel

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
private theorem rankOne_checked : ∀ x : Fin 10, entry c16 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 10))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  have h3 := Certificate.mul_mem Q c1 c2 c3 h1 h2 (by decide +kernel) check3
  have h4 := Certificate.mul_mem Q c3 c2 c4 h3 h2 (by decide +kernel) check4
  have h5 := Certificate.add_mem Q c0 c4 c5 h0 h4 check5
  have h6 := Certificate.mul_mem Q c4 c4 c6 h4 h4 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c5 c7 h6 h5 (by decide +kernel) check7
  have h8 := Certificate.add_mem Q c5 c7 c8 h5 h7 check8
  have h9 := Certificate.mul_mem Q c6 c6 c9 h6 h6 (by decide +kernel) check9
  have h10 := Certificate.add_mem Q c8 c9 c10 h8 h9 check10
  have h11 := Certificate.mul_mem Q c10 c2 c11 h10 h2 (by decide +kernel) check11
  have h12 := Certificate.mul_mem Q c11 c1 c12 h11 h1 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c2 c13 h12 h2 (by decide +kernel) check13
  have h14 := Certificate.mul_mem Q c13 c1 c14 h13 h1 (by decide +kernel) check14
  have h15 := Certificate.mul_mem Q c14 c2 c15 h14 h2 (by decide +kernel) check15
  have h16 := Certificate.mul_mem Q c15 c10 c16 h15 h10 (by decide +kernel) check16
  rw [← rankOne_eq c16 _ _ rankOne_checked]
  exact h16

/-- Density of the literal factor with orientation 1 and flag index 7. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 1 7)) (Fin (degree 1 7)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 1 7 j ∈ Q) : Q = ⊤ := by
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

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F17
