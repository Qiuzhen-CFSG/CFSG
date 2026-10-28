module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.FactorAlgebras.Certificate

/-!
# Checked density certificate for M12 induced-heart factor 6

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: James, J. Algebra 27 (1973), 57–111; Chapter K pp.451 and 457.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients.FactorAlgebras.F6
open Certificate CertificateData CertificateData.MatrixChecks

private def c0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

private def c1 : List ℕ := [72, 24, 12, 8, 10, 1015, 9, 136, 264, 520]

private def c2 : List ℕ := [96, 576, 80, 68, 72, 959, 192, 64, 66, 320]

private def c3 : List ℕ := [895, 384, 136, 144, 132, 129, 128, 192, 640, 130]

private def c4 : List ℕ := [894, 386, 140, 152, 148, 161, 192, 64, 896, 642]

private def c5 : List ℕ := [798, 962, 220, 220, 220, 798, 0, 0, 962, 962]

private def c6 : List ℕ := [790, 921, 143, 143, 143, 790, 0, 0, 921, 921]

private def c7 : List ℕ := [962, 798, 220, 220, 220, 962, 0, 0, 798, 798]

private def c8 : List ℕ := [220, 220, 0, 0, 0, 220, 0, 0, 220, 220]

private def colsList : List ℕ := [803, 880, 472, 604, 961, 993, 444, 633, 1000, 428]

private def rowsOrbitList : List ℕ := [220, 143, 628, 496, 821, 185, 915, 978, 906, 838]

private def ciList : List ℕ := [104, 655, 208, 328, 576, 48, 164, 522, 418, 884]

private def riList : List ℕ := [637, 962, 754, 60, 769, 531, 701, 883, 212, 345]

private def cpList : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8]

private def caList : List ℕ := [0, 1, 0, 1, 0, 1, 0, 1, 1]

private def rpList : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8]

private def raList : List ℕ := [0, 1, 0, 1, 0, 1, 0, 1, 1]

private def at0 : List ℕ := [96, 48, 36, 991, 34, 32, 33, 160, 288, 544]

private def at1 : List ℕ := [32, 288, 40, 48, 36, 33, 991, 96, 544, 34]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 9) : Fin 10 := ⟨entry cpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 9) : Fin 10 := ⟨entry rpList x.val % 10, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 9) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 9) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 10) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 10), entry (transposed j) y.val = actionColumns j (blockIndex 6 y) >>> cut 6 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 10) (actors j) = factorMatrix 6 j := by
  have h : (matrix (n := 10) (transposed j)).transpose = factorMatrix 6 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 6 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem check3 : ∀ x : Fin 10, combineList c2 (entry c2 x.val) = entry c3 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check4 : ∀ x : Fin 10, entry c0 x.val ^^^ entry c3 x.val = entry c4 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check5 : ∀ x : Fin 10, entry c4 x.val ^^^ entry c2 x.val = entry c5 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check6 : ∀ x : Fin 10, combineList c1 (entry c5 x.val) = entry c6 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check7 : ∀ x : Fin 10, combineList c5 (entry c6 x.val) = entry c7 x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check8 : ∀ x : Fin 10, entry c7 x.val ^^^ entry c5 x.val = entry c8 x.val := by decide +kernel

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
private theorem rankOne_checked : ∀ x : Fin 10, entry c8 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 10))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  have h3 := Certificate.mul_mem Q c2 c2 c3 h2 h2 (by decide +kernel) check3
  have h4 := Certificate.add_mem Q c0 c3 c4 h0 h3 check4
  have h5 := Certificate.add_mem Q c4 c2 c5 h4 h2 check5
  have h6 := Certificate.mul_mem Q c5 c1 c6 h5 h1 (by decide +kernel) check6
  have h7 := Certificate.mul_mem Q c6 c5 c7 h6 h5 (by decide +kernel) check7
  have h8 := Certificate.add_mem Q c7 c5 c8 h7 h5 check8
  rw [← rankOne_eq c8 _ _ rankOne_checked]
  exact h8

/-- Density of the literal induced-heart factor at flag index 6. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 6)) (Fin (degree 6)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 6 j ∈ Q) : Q = ⊤ := by
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

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients.FactorAlgebras.F6
