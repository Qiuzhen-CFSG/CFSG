module

public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions00
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions01
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions02
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions10
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions11
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions12
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions20
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions21
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transitions22
public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Transport
import Mathlib.Tactic.FinCases

/-!
# The certified E₉ × A₄ projective matrix table for O'Nan

All 432 right-generator products of the 108 explicit matrices are checked by
kernel reduction of sound GF(7) arithmetic certificates. Their scalars are
nonzero. The transport argument follows the actual canonical words from the
identity matrix and passes their linear lifts to the projective O'Nan model.
The existing first-row fingerprints then separate these projective elements.

The only remaining premise is that the four fixed word lifts equal the four
published generator matrices; the independent word certificate supplies this
premise to the subgroup-embedding assembly. No order or simplicity assumption
on O'Nan, and no subgroup-family label, enters this proof.

Sources: Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.19,
printed p. 41; ATLAS 45a matrices and max5 words, `E9A4/source/README.md`.
-/

public section
namespace ONan.E9A4
open Theory.SpecificGroups.E9A4 (Coord next)

/-- The complete matrix transition table, with the scalar on the right. -/
theorem Data.table_mul_generator (c : Coord) (i : Fin 4) :
    Data.table c * Data.generatorMatrix i = Data.scalar c i • Data.table (next c i) := by
  obtain ⟨⟨a, b⟩, k⟩ := c
  fin_cases a <;> fin_cases b
  · exact MatrixTable.transitions_0_0 k i
  · exact MatrixTable.transitions_0_1 k i
  · exact MatrixTable.transitions_0_2 k i
  · exact MatrixTable.transitions_1_0 k i
  · exact MatrixTable.transitions_1_1 k i
  · exact MatrixTable.transitions_1_2 k i
  · exact MatrixTable.transitions_2_0 k i
  · exact MatrixTable.transitions_2_1 k i
  · exact MatrixTable.transitions_2_2 k i

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Every transition scalar defines an invertible scalar matrix. -/
theorem Data.scalar_ne_zero : ∀ (c : Coord) (i : Fin 4), Data.scalar c i ≠ 0 := by
  decide +kernel

/-- Word realization transports the certified transitions to the actual projective model. -/
theorem normalForm_next_of_realization
    (hgen : ∀ i, (linearGenerators i : Mat) = Data.generatorMatrix i)
    (c : Coord) (i : Fin 4) : normalForm (next c i) = normalForm c * generators i :=
  MatrixTable.normalForm_next_of_table hgen Data.table_mul_generator Data.scalar_ne_zero c i

/-- Word realization and projective matrix separation make the actual normal forms faithful. -/
theorem normalForm_injective_of_realization
    (hgen : ∀ i, (linearGenerators i : Mat) = Data.generatorMatrix i) :
    Function.Injective normalForm :=
  MatrixTable.normalForm_injective_of_table hgen Data.table_mul_generator Data.scalar_ne_zero

end ONan.E9A4
