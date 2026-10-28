module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Checked density certificate for Hermitian factor 06

The straight-line products give a rank-one element of the generated algebra.
Checked row and column orbit bases then give every matrix unit. All packed
identities are checked by the kernel against the literal diagonal block.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F06
open Certificate MatrixChecks

private def c0 : List ℕ := [1]

private def c1 : List ℕ := [1]

private def c2 : List ℕ := [1]

private def colsList : List ℕ := [1]

private def rowsOrbitList : List ℕ := [1]

private def ciList : List ℕ := [1]

private def riList : List ℕ := [1]

private def cpList : List ℕ := []

private def caList : List ℕ := []

private def rpList : List ℕ := []

private def raList : List ℕ := []

private def at0 : List ℕ := [1]

private def at1 : List ℕ := [1]

private def actors : Fin 2 → List ℕ := ![c1, c2]
private def transposed : Fin 2 → List ℕ := ![at0, at1]

private def cp (x : Fin 0) : Fin 1 := ⟨entry cpList x.val % 1, Nat.mod_lt _ (by decide)⟩

private def rp (x : Fin 0) : Fin 1 := ⟨entry rpList x.val % 1, Nat.mod_lt _ (by decide)⟩

private def ca (x : Fin 0) : Fin 2 := ⟨entry caList x.val % 2, Nat.mod_lt _ (by decide)⟩

private def ra (x : Fin 0) : Fin 2 := ⟨entry raList x.val % 2, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem transpose_checked : ∀ j : Fin 2, matrix (n := 1) (transposed j) = (matrix (actors j)).transpose := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_columns : ∀ (j : Fin 2) (y : Fin 1), entry (transposed j) y.val = actionColumns 0 j (blockIndex 0 6 y) >>> cut 0 6 := by decide +kernel

private theorem actors_checked (j : Fin 2) :
    matrix (n := 1) (actors j) = factorMatrix 0 6 j := by
  have h : (matrix (n := 1) (transposed j)).transpose = factorMatrix 0 6 j := by
    ext x y
    change bit (entry (transposed j) y.val) x.val = _
    rw [packed_columns]
    exact factorMatrix_entry_shift 0 6 j x y
  rw [transpose_checked, transpose_transpose] at h
  exact h

set_option maxRecDepth 8192 in
private theorem cparent : ∀ x : Fin 0, cp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cstep : ∀ x : Fin 0, combineList (transposed (ca x)) (entry colsList (cp x).val) = entry colsList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cinverse : ∀ x : Fin 1, combineList colsList (entry ciList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rparent : ∀ x : Fin 0, rp x < x.succ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rstep : ∀ x : Fin 0, combineList (actors (ra x)) (entry rowsOrbitList (rp x).val) = entry rowsOrbitList x.succ.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rinverse : ∀ x : Fin 1, combineList rowsOrbitList (entry riList x.val) = 2 ^ x.val := by decide +kernel

set_option maxRecDepth 8192 in
private theorem rankOne_checked : ∀ x : Fin 1, entry c0 x.val = if (entry colsList 0).testBit x.val then entry rowsOrbitList 0 else 0 := by decide +kernel

private theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 1))
    (hA : ∀ j : Fin 2, matrix (actors j) ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  have h0 := Certificate.one_mem Q c0 (by decide +kernel)
  have h1 : matrix c1 ∈ Q := hA 0
  have h2 : matrix c2 ∈ Q := hA 1
  rw [← rankOne_eq c0 _ _ rankOne_checked]
  exact h0

/-- Density of the literal factor with orientation 0 and flag index 6. -/
theorem full (Q : Subalgebra (ZMod 2)
    (Matrix (Fin (degree 0 6)) (Fin (degree 0 6)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix 0 6 j ∈ Q) : Q = ⊤ := by
  have hA' : ∀ j : Fin 2, matrix (n := 1) (actors j) ∈ Q := by
    intro j
    rw [actors_checked]
    exact hA j
  apply full_of_orbits (m := 0) Q (fun j => matrix (n := 1) (actors j)) hA'
    colsList rowsOrbitList ciList riList cp rp ca ra cparent rparent
  · intro x
    have h := congrArg (vector (n := 1)) (cstep x)
    rw [vector_combine _ (show (transposed (ca x)).length = 1 from by
      generalize ca x = j; revert j; decide +kernel), transpose_checked,
      vecMul_transpose] at h
    exact h
  · intro x
    have h := congrArg (vector (n := 1)) (rstep x)
    rw [vector_combine _ (show (actors (ra x)).length = 1 from by
      generalize ra x = j; revert j; decide +kernel)] at h
    exact h
  · decide +kernel
  · decide +kernel
  · exact cinverse
  · exact rinverse
  · exact rankOne_mem Q hA'

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F06
