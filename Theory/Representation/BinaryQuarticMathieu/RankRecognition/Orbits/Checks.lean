module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Boolean
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Maps
public import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for the three basis evaluations

For each increasing quadruple, the quartic on its standard basis vectors and
on each of the two sets of image columns has the same published coefficient.
These checks use the proved Boolean evaluator and cover all 210 quadruples.
Fourteen-element rows keep each reduction small. The matrices originate in
`../../source/orbit-witnesses.json`; their assertions are not assumed.
-/

public section
namespace BinaryQuarticMathieu.RankRecognition.Orbits

private theorem checkByRows (P : Fin 210 → Prop)
    (h : ∀ a : Fin 15, ∀ b : Fin 14, P ⟨a.val * 14 + b.val, by omega⟩)
    (i : Fin 210) : P i := by
  have hh := h ⟨i.val / 14, by omega⟩ ⟨i.val % 14, Nat.mod_lt _ (by decide)⟩
  have he : (⟨i.val / 14 * 14 + i.val % 14, by omega⟩ : Fin 210) = i := by
    apply Fin.ext
    change i.val / 14 * 14 + i.val % 14 = i.val
    omega
  simpa only [he] using hh

theorem basisVector_word : ∀ i : Fin 10, basisVector i = vector (2 ^ i.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row0 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨0 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (0 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row1 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨1 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (1 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row2 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨2 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (2 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row3 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨3 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (3 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row4 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨4 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (4 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row5 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨5 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (5 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row6 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨6 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (6 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row7 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨7 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (7 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row8 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨8 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (8 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row9 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨9 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (9 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row10 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨10 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (10 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row11 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨11 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (11 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row12 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨12 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (12 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row13 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨13 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (13 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem basis_values_row14 : ∀ b : Fin 14,
    boolQuartic (fun j => 2 ^ (fastQuad (⟨14 * 14 + b.val, by omega⟩ : Fin 210) j).val) =
      coefficientWord.testBit (14 * 14 + b.val) := by
  decide +kernel

theorem basis_values : ∀ i : Fin 210,
    boolQuartic (fun j => 2 ^ (fastQuad i j).val) = coefficientWord.testBit i.val := by
  refine checkByRows (fun i => boolQuartic (fun j => 2 ^ (fastQuad i j).val) = coefficientWord.testBit i.val) ?_
  intro a
  fin_cases a
  · exact basis_values_row0
  · exact basis_values_row1
  · exact basis_values_row2
  · exact basis_values_row3
  · exact basis_values_row4
  · exact basis_values_row5
  · exact basis_values_row6
  · exact basis_values_row7
  · exact basis_values_row8
  · exact basis_values_row9
  · exact basis_values_row10
  · exact basis_values_row11
  · exact basis_values_row12
  · exact basis_values_row13
  · exact basis_values_row14

set_option maxRecDepth 4096 in
private theorem generatorA_values_row0 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨0 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (0 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row1 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨1 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (1 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row2 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨2 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (2 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row3 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨3 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (3 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row4 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨4 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (4 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row5 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨5 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (5 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row6 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨6 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (6 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row7 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨7 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (7 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row8 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨8 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (8 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row9 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨9 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (9 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row10 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨10 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (10 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row11 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨11 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (11 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row12 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨12 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (12 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row13 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨13 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (13 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorA_values_row14 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsA (fastQuad (⟨14 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (14 * 14 + b.val) := by
  decide +kernel

theorem generatorA_values : ∀ i : Fin 210,
    boolQuartic (fun j => columnsA (fastQuad i j)) = coefficientWord.testBit i.val := by
  refine checkByRows (fun i => boolQuartic (fun j => columnsA (fastQuad i j)) = coefficientWord.testBit i.val) ?_
  intro a
  fin_cases a
  · exact generatorA_values_row0
  · exact generatorA_values_row1
  · exact generatorA_values_row2
  · exact generatorA_values_row3
  · exact generatorA_values_row4
  · exact generatorA_values_row5
  · exact generatorA_values_row6
  · exact generatorA_values_row7
  · exact generatorA_values_row8
  · exact generatorA_values_row9
  · exact generatorA_values_row10
  · exact generatorA_values_row11
  · exact generatorA_values_row12
  · exact generatorA_values_row13
  · exact generatorA_values_row14

set_option maxRecDepth 4096 in
private theorem generatorB_values_row0 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨0 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (0 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row1 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨1 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (1 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row2 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨2 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (2 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row3 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨3 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (3 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row4 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨4 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (4 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row5 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨5 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (5 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row6 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨6 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (6 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row7 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨7 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (7 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row8 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨8 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (8 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row9 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨9 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (9 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row10 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨10 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (10 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row11 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨11 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (11 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row12 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨12 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (12 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row13 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨13 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (13 * 14 + b.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem generatorB_values_row14 : ∀ b : Fin 14,
    boolQuartic (fun j => columnsB (fastQuad (⟨14 * 14 + b.val, by omega⟩ : Fin 210) j)) =
      coefficientWord.testBit (14 * 14 + b.val) := by
  decide +kernel

theorem generatorB_values : ∀ i : Fin 210,
    boolQuartic (fun j => columnsB (fastQuad i j)) = coefficientWord.testBit i.val := by
  refine checkByRows (fun i => boolQuartic (fun j => columnsB (fastQuad i j)) = coefficientWord.testBit i.val) ?_
  intro a
  fin_cases a
  · exact generatorB_values_row0
  · exact generatorB_values_row1
  · exact generatorB_values_row2
  · exact generatorB_values_row3
  · exact generatorB_values_row4
  · exact generatorB_values_row5
  · exact generatorB_values_row6
  · exact generatorB_values_row7
  · exact generatorB_values_row8
  · exact generatorB_values_row9
  · exact generatorB_values_row10
  · exact generatorB_values_row11
  · exact generatorB_values_row12
  · exact generatorB_values_row13
  · exact generatorB_values_row14

end BinaryQuarticMathieu.RankRecognition.Orbits
