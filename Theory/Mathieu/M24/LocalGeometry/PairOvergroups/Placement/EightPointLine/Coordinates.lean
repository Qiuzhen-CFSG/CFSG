module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Model
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.TripleData

/-!
# Coordinates for the elementary nines on eight letters

Each candidate consists of two disjoint three-cycles on the listed triples.
The generators are even, commute, and have cube one. Evaluating a normal
form at the first letter of each triple recovers its two exponents, proving
injectivity without comparing every pair of words. All finite identities
are checked by Lean's kernel; the Python diagnostics are not used.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511;
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
open Subgroup

/-- The two three-cycles on a pair of triples, before restriction to A₈. -/
def rawNineGenerator (i : Fin 280) (k : Fin 2) : Sym :=
  if k = 0 then
    Equiv.swap (triplePair i 0) (triplePair i 1) *
      Equiv.swap (triplePair i 1) (triplePair i 2)
  else
    Equiv.swap (triplePair i 3) (triplePair i 4) *
      Equiv.swap (triplePair i 4) (triplePair i 5)

set_option maxRecDepth 10000 in
private theorem triplePair_adjacent_distinct : ∀ i,
    triplePair i 0 ≠ triplePair i 1 ∧ triplePair i 1 ≠ triplePair i 2 ∧
    triplePair i 3 ≠ triplePair i 4 ∧ triplePair i 4 ≠ triplePair i 5 := by
  decide +kernel

theorem rawNineGenerator_even (i : Fin 280) (k : Fin 2) :
    rawNineGenerator i k ∈ alternatingGroup (Fin 8) := by
  obtain ⟨h01, h12, h34, h45⟩ := triplePair_adjacent_distinct i
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold rawNineGenerator
  split_ifs <;> simp [h01, h12, h34, h45]

/-- The two independent three-cycles, as elements of the actual A₈. -/
def nineGenerator (i : Fin 280) (k : Fin 2) : Alt :=
  ⟨rawNineGenerator i k, rawNineGenerator_even i k⟩

/-- Its nine normal forms. -/
def nineWord (i : Fin 280) (j : Fin 9) : Alt :=
  nineGenerator i 0 ^ (j.val % 3) * nineGenerator i 1 ^ (j.val / 3)

set_option maxRecDepth 10000 in
theorem nineGenerator_cube : ∀ i k, nineGenerator i k ^ 3 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem nineGenerator_commute : ∀ i,
    Commute (nineGenerator i 0) (nineGenerator i 1) := by
  change ∀ i, nineGenerator i 0 * nineGenerator i 1 =
    nineGenerator i 1 * nineGenerator i 0
  decide +kernel

private def nineWordIndex (i : Fin 280) (g : Alt) : ℕ :=
  (if g.val (triplePair i 0) = triplePair i 0 then 0
    else if g.val (triplePair i 0) = triplePair i 1 then 1 else 2) +
  3 * (if g.val (triplePair i 3) = triplePair i 3 then 0
    else if g.val (triplePair i 3) = triplePair i 4 then 1 else 2)

set_option maxRecDepth 10000 in
private theorem nineWordIndex_word : ∀ i j, nineWordIndex i (nineWord i j) = j.val := by
  decide +kernel

theorem nineWord_injective (i : Fin 280) : Function.Injective (nineWord i) := by
  intro j k h
  apply Fin.ext
  simpa only [nineWordIndex_word] using congrArg (nineWordIndex i) h

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
end
