module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 13

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F13
open Certificate MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [990, 295, 987, 983, 150, 37, 793, 634, 261, 474]

private def c2 : List ℕ := [785, 512, 58, 899, 528, 270, 843, 907, 11, 2]

private def c3 : List ℕ := [864, 46, 75, 1010, 929, 549, 651, 468, 800, 856]

private def c4 : List ℕ := [588, 183, 473, 471, 413, 551, 283, 737, 263, 721]

private def c5 : List ℕ := [719, 1003, 249, 466, 59, 221, 189, 834, 39, 1009]

private def c6 : List ℕ := [618, 853, 844, 219, 396, 632, 61, 322, 37, 198]

private def c7 : List ℕ := [22, 853, 970, 219, 883, 423, 865, 827, 32, 927]

private def c8 : List ℕ := [42, 633, 330, 66, 333, 933, 349, 389, 270, 826]

private def c9 : List ℕ := [141, 197, 707, 331, 1000, 423, 504, 171, 434, 660]

private def c10 : List ℕ := [803, 1003, 467, 466, 580, 933, 86, 23, 670, 419]

private def c11 : List ℕ := [802, 1001, 471, 474, 596, 901, 22, 151, 926, 931]

private def c12 : List ℕ := [80, 451, 83, 880, 38, 639, 42, 863, 26, 484]

private def c13 : List ℕ := [578, 980, 649, 506, 443, 674, 438, 697, 103, 333]

private def c14 : List ℕ := [352, 61, 862, 32, 1007, 295, 416, 558, 1017, 750]

private def c15 : List ℕ := [12, 764, 415, 909, 1007, 295, 204, 834, 661, 323]

private def c16 : List ℕ := [364, 705, 705, 941, 0, 0, 364, 364, 364, 941]

private def c17 : List ℕ := [503, 979, 979, 548, 0, 0, 503, 503, 503, 548]

private def c18 : List ℕ := [766, 968, 968, 310, 0, 0, 766, 766, 766, 310]

private def c19 : List ℕ := [289, 619, 619, 842, 0, 0, 289, 289, 289, 842]

private def c20 : List ℕ := [0, 705, 705, 705, 0, 0, 0, 0, 0, 705]

private def colsList : List ℕ := [526, 428, 755, 417, 467, 551, 158, 529, 693, 894]

private def rowsOrbitList : List ℕ := [705, 871, 979, 968, 619, 842, 213, 310, 496, 507]

private def ciList : List ℕ := [362, 444, 839, 551, 311, 876, 1023, 427, 933, 221]

private def riList : List ℕ := [363, 935, 368, 460, 780, 501, 216, 911, 174, 573]

private def cpList : List ℕ := [0, 0, 1, 2, 2, 3, 4, 6, 7]

private def caList : List ℕ := [0, 1, 1, 0, 1, 0, 1, 1, 0]

private def rpList : List ℕ := [0, 0, 2, 3, 3, 4, 5, 6, 6]

private def raList : List ℕ := [0, 1, 1, 0, 1, 1, 0, 0, 1]

private def at0 : List ℕ := [366, 671, 315, 709, 733, 162, 653, 541, 847, 205]

private def at1 : List ℕ := [457, 1004, 32, 484, 21, 4, 64, 136, 233, 219]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns 1 j (blockIndex 1 3 y) >>> cut 1 3 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 1 3 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 1 3 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 1 3 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 10, combineList c2 (entry c1 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 10, combineList c2 (entry c3 x.val) = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 10, combineList c1 (entry c4 x.val) = entry c5 x.val := by decide +kernel

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
private theorem check18 : ∀ x : Fin 10, combineList c2 (entry c17 x.val) = entry c18 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check19 : ∀ x : Fin 10, combineList c1 (entry c18 x.val) = entry c19 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check20 : ∀ x : Fin 10, combineList c16 (entry c19 x.val) = entry c20 x.val := by decide +kernel

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
private theorem rankOne_checked : ∀ x : Fin 10, entry c20 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 10))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  have h3 := Certificate.mul_mem Q c1 c2 c3 h1 h2 (by decide +kernel) check3
  have h4 := Certificate.mul_mem Q c3 c2 c4 h3 h2 (by decide +kernel) check4
  have h5 := Certificate.mul_mem Q c4 c1 c5 h4 h1 (by decide +kernel) check5
  have h6 := Certificate.mul_mem Q c5 c2 c6 h5 h2 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c1 c7 h6 h1 (by decide +kernel) check7
  have h8 := Certificate.mul_mem Q c7 c2 c8 h7 h2 (by decide +kernel) check8
  have h9 := Certificate.mul_mem Q c8 c2 c9 h8 h2 (by decide +kernel) check9
  have h10 := Certificate.mul_mem Q c9 c2 c10 h9 h2 (by decide +kernel) check10
  have h11 := Certificate.add_mem Q c0 c10 c11 h0 h10 check11
  have h12 := Certificate.mul_mem Q c10 c10 c12 h10 h10 (by decide +kernel) check12
  have h13 := Certificate.mul_mem Q c12 c11 c13 h12 h11 (by decide +kernel) check13
  have h14 := Certificate.add_mem Q c11 c13 c14 h11 h13 check14
  have h15 := Certificate.mul_mem Q c12 c12 c15 h12 h12 (by decide +kernel) check15
  have h16 := Certificate.add_mem Q c14 c15 c16 h14 h15 check16
  have h17 := Certificate.mul_mem Q c16 c2 c17 h16 h2 (by decide +kernel) check17
  have h18 := Certificate.mul_mem Q c17 c2 c18 h17 h2 (by decide +kernel) check18
  have h19 := Certificate.mul_mem Q c18 c1 c19 h18 h1 (by decide +kernel) check19
  have h20 := Certificate.mul_mem Q c19 c16 c20 h19 h16 (by decide +kernel) check20
  rw [← rankOne_eq c20 _ _ rankOne_checked]
  exact h20

/-- Density of the literal factor with orientation 1 and flag index 3. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 1 3)) (Fin (degree 1 3)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 1 3 j ∈ Q) : Q = ⊤ := by
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

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F13
