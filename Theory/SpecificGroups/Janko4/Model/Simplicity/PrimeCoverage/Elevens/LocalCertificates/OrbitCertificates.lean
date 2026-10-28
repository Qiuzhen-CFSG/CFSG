module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.OrbitData
import Mathlib.Tactic.FinCases

/-!
# Kernel-checked cyclic orbit coverage

For each of the 1330 nonidentity coordinate triples, the witness table gives
an exponent and a word in the four actions taking that power to `Z` or `X`.
The eleven row certificates check all entries by reduction in the kernel.
`cyclic_coverage` exposes only the mathematical existence statement.

The underlying coordinate group and actions are proved in `Coordinates`;
matching them with the ATLAS matrix words is a separate obligation.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens.LocalCoordinates

private def checkWitness (c : Coord) (w : OrbitWitness) : Bool :=
  decide (c = 1 ∨ representative w.1 = wordHom w.2.2 (c ^ w.2.1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row0 : ∀ j k : Fin 11,
    checkWitness ⟨0, j, k⟩ (orbitRow0.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row1 : ∀ j k : Fin 11,
    checkWitness ⟨1, j, k⟩ (orbitRow1.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row2 : ∀ j k : Fin 11,
    checkWitness ⟨2, j, k⟩ (orbitRow2.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row3 : ∀ j k : Fin 11,
    checkWitness ⟨3, j, k⟩ (orbitRow3.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row4 : ∀ j k : Fin 11,
    checkWitness ⟨4, j, k⟩ (orbitRow4.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row5 : ∀ j k : Fin 11,
    checkWitness ⟨5, j, k⟩ (orbitRow5.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row6 : ∀ j k : Fin 11,
    checkWitness ⟨6, j, k⟩ (orbitRow6.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row7 : ∀ j k : Fin 11,
    checkWitness ⟨7, j, k⟩ (orbitRow7.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row8 : ∀ j k : Fin 11,
    checkWitness ⟨8, j, k⟩ (orbitRow8.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row9 : ∀ j k : Fin 11,
    checkWitness ⟨9, j, k⟩ (orbitRow9.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_row10 : ∀ j k : Fin 11,
    checkWitness ⟨10, j, k⟩ (orbitRow10.get ⟨11*j.val+k.val, by omega⟩) = true := by
  decide +kernel

private def orbitRows : Fin 11 → Vector OrbitWitness 121 :=
  ![orbitRow0, orbitRow1, orbitRow2, orbitRow3, orbitRow4, orbitRow5, orbitRow6, orbitRow7, orbitRow8, orbitRow9, orbitRow10]

private theorem check_all (i j k : Fin 11) :
    checkWitness ⟨i, j, k⟩ ((orbitRows i).get ⟨11*j.val+k.val, by omega⟩) = true := by
  fin_cases i
  · exact check_row0 j k
  · exact check_row1 j k
  · exact check_row2 j k
  · exact check_row3 j k
  · exact check_row4 j k
  · exact check_row5 j k
  · exact check_row6 j k
  · exact check_row7 j k
  · exact check_row8 j k
  · exact check_row9 j k
  · exact check_row10 j k

/-- Every nonidentity coordinate has a power carried to `Z` or `X` by the
four specified actions. This checks all coordinates, not just projective ones. -/
theorem cyclic_coverage (c : Coord) (hc : c ≠ 1) :
    ∃ (j : Fin 2) (n : ℕ) (l : List (Fin 4)),
      representative j = wordHom l (c ^ n) := by
  rcases c with ⟨i, j, k⟩
  have h := check_all i j k
  have hh := of_decide_eq_true h
  rcases hh with h1 | h1
  · exact (hc h1).elim
  · exact ⟨_, _, _, h1⟩

end Janko4.Simplicity.Elevens.LocalCoordinates
