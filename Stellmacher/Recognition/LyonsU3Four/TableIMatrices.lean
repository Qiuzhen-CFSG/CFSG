module

public import Stellmacher.Recognition.LyonsU3Four.TableIBlocks

/-!
# The explicit matrices of Lyons's Table I

This is an enumeration of the twenty printed cases, with both Z₁/Z₂ choices
for A–E, hence twenty-five matrices. It does not assert exhaustiveness for
arbitrary generalized decomposition data. In particular, it does not use the
unconstrained matrix field of `TableIPatternWitness` as a canonical matrix.

Rows and repeated blocks appear in printed order. Row zero is principal in
every case. The dependent `TableICase.Variant` interface allows precisely
the two printed choices for A–E and a unique choice for each other case.
The matrix bodies are exposed so numerical elimination can evaluate columns.
Finite calculations verify the Gram, strict contribution, and congruence
identities; an explicit row permutation verifies Galois symmetry.

There is one source correction: p. 375 prints `+2` for `dᵗ` in the y₃ row
of J (zero-based row 9). This contradicts (3.2): its inner product with ₁dᶻ
is 8. The derivation in Case 5(c), p. 379, explicitly requires `dᵗ = −₁dᶻ`
there, namely `−2`. The canonical
`tableIMatrix` uses `−2`, and all its numerical hypotheses are verified.
`tableIPrintedMatrix` and `TableICatalogue.rowsJPrinted` retain the literal
`+2`; `tableIPrintedData_equation3_2_iff` records exactly where the printed
catalogue fails (3.2). No other entry is changed.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I, pp. 374–377. Checked against all four page images in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
The continuations of L and M at the top of p. 376 are included.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

/-- Number of rows, including all repetitions and the principal row. -/
def tableIRowCount : TableICase → ℕ
  | .A => 10
  | .B => 11
  | .C => 12
  | .D => 13
  | .E => 15
  | .F => 15
  | .G => 13
  | .H => 13
  | .J => 14
  | .K => 13
  | .L => 15
  | .M => 21
  | .N => 21
  | .P => 23
  | .Q => 21
  | .R => 23
  | .S => 19
  | .T => 17
  | .U => 18
  | .V => 21

/-- Every printed matrix has a principal row. -/
instance (c : TableICase) : NeZero (tableIRowCount c) :=
  ⟨by cases c <;> decide⟩

/-- Valid variants: `.z1` or `.z2` for A–E, and `()` otherwise. -/
def TableICase.Variant : TableICase → Type
  | .A | .B | .C | .D | .E => TableICatalogue.ZChoice
  | _ => Unit

namespace TableICatalogue

/-- Case A, in printed order with every repeated row retained. -/
def rowsA (v : ZChoice) : TableIMatrix (Fin 10) :=
  Fin.append (initial v) (![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 2, 2, 2, 2],
  ![2, 2, 2, 2, 2, 2]])

/-- Case B, in printed order with every repeated row retained. -/
def rowsB (v : ZChoice) : TableIMatrix (Fin 11) :=
  Fin.append (initial v) (![
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![2, 2, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case C, in printed order with every repeated row retained. -/
def rowsC (v : ZChoice) : TableIMatrix (Fin 12) :=
  Fin.append (initial v) (![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![2, 2, 2, 2, 2, 2],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case D, in printed order with every repeated row retained. -/
def rowsD (v : ZChoice) : TableIMatrix (Fin 13) :=
  Fin.append (initial v) (![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2]])

/-- Case E, in printed order with every repeated row retained. -/
def rowsE (v : ZChoice) : TableIMatrix (Fin 15) :=
  Fin.append (initial v) (![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case F, in printed order with every repeated row retained. -/
def rowsF : TableIMatrix (Fin 15) :=
  Fin.append (z3) (![
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case G, in printed order with every repeated row retained. -/
def rowsG : TableIMatrix (Fin 13) :=
  Fin.append (z3) (![
  ![1, 1, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0]])

/-- Case H, in printed order with every repeated row retained. -/
def rowsH : TableIMatrix (Fin 13) :=
  Fin.append (z4) (![
  ![0, 2, 2, 1, 2, 1],
  ![0, 2, 1, 2, 1, 2],
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case J in printed row order, correcting the single entry `dᵗ₉` from
`+2` to `−2` as required by (3.2) and the derivation on p. 379.
The literal transcription is `rowsJPrinted`. -/
def rowsJ : TableIMatrix (Fin 14) :=
  Fin.append (z4) (![
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-1, 1, 2, 1, 2, 1],
  ![-1, 1, 1, 2, 1, 2],
  ![-2, 2, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1]])

/-- Case K, in printed order with every repeated row retained. -/
def rowsK : TableIMatrix (Fin 13) :=
  Fin.append (z4) (![
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-2, 2, 2, 2, 2, 2],
  ![1, 1, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0]])

/-- Case L, in printed order with every repeated row retained. -/
def rowsL : TableIMatrix (Fin 15) :=
  Fin.append (z4) (![
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![-2, 2, 2, 2, 2, 2],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])

/-- Case M, in printed order with every repeated row retained. -/
def rowsM : TableIMatrix (Fin 21) :=
  Fin.append (![
  ![1, 1, 0, 0, 0, 0]]) (Fin.append (z5) (Fin.append (z5) (Fin.append (z5) (Fin.append (z6) (![
  ![-1, 3, 3, 3, 3, 3],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1]])))))

/-- Case N, in printed order with every repeated row retained. -/
def rowsN : TableIMatrix (Fin 21) :=
  Fin.append (![
  ![1, 1, 0, 0, 0, 0]]) (Fin.append (z5) (Fin.append (z5) (Fin.append (z6) (Fin.append (z6) (![
  ![-2, 2, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0]])))))

/-- Case P, in printed order with every repeated row retained. -/
def rowsP : TableIMatrix (Fin 23) :=
  Fin.append (![
  ![1, 1, 0, 0, 0, 0]]) (Fin.append (z5) (Fin.append (z5) (Fin.append (z6) (Fin.append (z6) (![
  ![-2, 2, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])))))

/-- Case Q, in printed order with every repeated row retained. -/
def rowsQ : TableIMatrix (Fin 21) :=
  Fin.append (![
  ![1, 1, 0, 0, 0, 0]]) (Fin.append (z5) (Fin.append (z6) (Fin.append (z6) (Fin.append (z6) (![
  ![-3, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1]])))))

/-- Case R, in printed order with every repeated row retained. -/
def rowsR : TableIMatrix (Fin 23) :=
  Fin.append (![
  ![1, 1, 0, 0, 0, 0]]) (Fin.append (z5) (Fin.append (z6) (Fin.append (z6) (Fin.append (z6) (![
  ![-3, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])))))

/-- Case S, in printed order with every repeated row retained. -/
def rowsS : TableIMatrix (Fin 19) :=
  Fin.append (z7) (Fin.append (z6) (Fin.append (z6) (![
  ![-2, 0, 1, 0, 1, 0],
  ![-2, 0, 0, 1, 0, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1]])))

/-- Case T, in printed order with every repeated row retained. -/
def rowsT : TableIMatrix (Fin 17) :=
  Fin.append (z7) (Fin.append (z6) (Fin.append (z5) (![
  ![-1, 1, 2, 1, 2, 1],
  ![-1, 1, 1, 2, 1, 2],
  ![1, 1, 2, 2, 2, 2],
  ![2, 2, 1, 1, 1, 1]])))

/-- Case U, in printed order with every repeated row retained. -/
def rowsU : TableIMatrix (Fin 18) :=
  Fin.append (z7) (Fin.append (z6) (Fin.append (z5) (![
  ![-1, 1, 2, 1, 2, 1],
  ![-1, 1, 1, 2, 1, 2],
  ![2, 2, 2, 2, 2, 2],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1]])))

/-- Case V, in printed order with every repeated row retained. -/
def rowsV : TableIMatrix (Fin 21) :=
  Fin.append (z7) (Fin.append (z6) (Fin.append (z5) (![
  ![-1, 1, 2, 1, 2, 1],
  ![-1, 1, 1, 2, 1, 2],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1]])))

end TableICatalogue

/-- The canonical finite matrix for a case and a valid variant.
J includes the documented `dᵗ₉ = −2` correction; `tableIPrintedMatrix` retains
the literal printing. -/
def tableIMatrix : (c : TableICase) → c.Variant → TableIMatrix (Fin (tableIRowCount c))
  | .A, v => TableICatalogue.rowsA v
  | .B, v => TableICatalogue.rowsB v
  | .C, v => TableICatalogue.rowsC v
  | .D, v => TableICatalogue.rowsD v
  | .E, v => TableICatalogue.rowsE v
  | .F, _ => TableICatalogue.rowsF
  | .G, _ => TableICatalogue.rowsG
  | .H, _ => TableICatalogue.rowsH
  | .J, _ => TableICatalogue.rowsJ
  | .K, _ => TableICatalogue.rowsK
  | .L, _ => TableICatalogue.rowsL
  | .M, _ => TableICatalogue.rowsM
  | .N, _ => TableICatalogue.rowsN
  | .P, _ => TableICatalogue.rowsP
  | .Q, _ => TableICatalogue.rowsQ
  | .R, _ => TableICatalogue.rowsR
  | .S, _ => TableICatalogue.rowsS
  | .T, _ => TableICatalogue.rowsT
  | .U, _ => TableICatalogue.rowsU
  | .V, _ => TableICatalogue.rowsV

/-- The distinguished principal row is always the first printed row. -/
def tableIPrincipal (c : TableICase) : Fin (tableIRowCount c) :=
  ⟨0, by cases c <;> decide⟩

/-- The six canonical columns, on exactly the finite printed row type. -/
def tableIData (c : TableICase) (v : c.Variant) :
    GeneralizedDecompositionData (Fin (tableIRowCount c)) where
  dT j := tableIMatrix c v j 0
  iDz i j := tableIMatrix c v j i.succ

@[simp] theorem tableIData_dT (c : TableICase) (v : c.Variant)
    (j : Fin (tableIRowCount c)) : (tableIData c v).dT j = tableIMatrix c v j 0 := rfl

@[simp] theorem tableIData_iDz (c : TableICase) (v : c.Variant)
    (i : Fin 5) (j : Fin (tableIRowCount c)) :
    (tableIData c v).iDz i j = tableIMatrix c v j i.succ := rfl

@[simp] theorem tableIData_tableIRow (c : TableICase) (v : c.Variant)
    (j : Fin (tableIRowCount c)) : (tableIData c v).tableIRow j = tableIMatrix c v j := by
  ext k
  fin_cases k <;> rfl

/-- Principal-row normalization, independent of case and variant. -/
theorem tableIMatrix_principal (c : TableICase) (v : c.Variant) :
    tableIMatrix c v (tableIPrincipal c) = ![1, 1, 0, 0, 0, 0] := by
  cases c <;> cases v <;> decide

/-- Equation (3.2): the complete six-column Gram identities. -/
theorem tableIData_equation3_2 (c : TableICase) (v : c.Variant) :
    (tableIData c v).Equation3_2 := by
  cases c <;> cases v <;> constructor <;> decide

/-- Equation (3.3): every printed row has contribution strictly below 64. -/
theorem tableIData_contributionBound (c : TableICase) (v : c.Variant) :
    (tableIData c v).ContributionBound := by
  unfold ContributionBound
  cases c <;> cases v <;> decide

/-- Equation (3.4): the order-four value and the sum of the other columns
are congruent modulo four, in every printed row. -/
theorem tableIData_equation3_4 (c : TableICase) (v : c.Variant) :
    (tableIData c v).Equation3_4 := by
  unfold Equation3_4
  cases c <;> cases v <;> decide

/-- Every row has nonzero value at the involution. -/
theorem tableIData_z_nonzero (c : TableICase) (v : c.Variant) :
    ∀ j, (tableIData c v).zValue j ≠ 0 := by
  cases c <;> cases v <;> decide

/-- Row permutation realizing the Galois rotation of the last four columns.
Equal rows are matched in their printed order, preserving their multiplicity. -/
def tableIGaloisNext : (c : TableICase) → Fin (tableIRowCount c) → Fin (tableIRowCount c)
  | .A => ![0, 2, 3, 4, 1, 5, 6, 7, 8, 9]
  | .B => ![0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10]
  | .C => ![0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11]
  | .D => ![0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 12]
  | .E => ![0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  | .F => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14]
  | .G => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 9, 10, 11, 12]
  | .H => ![0, 2, 3, 4, 1, 6, 5, 8, 7, 9, 10, 11, 12]
  | .J => ![0, 2, 3, 4, 1, 6, 5, 8, 7, 9, 10, 11, 12, 13]
  | .K => ![0, 2, 3, 4, 1, 6, 5, 8, 7, 9, 10, 11, 12]
  | .L => ![0, 2, 3, 4, 1, 6, 5, 8, 7, 9, 10, 11, 12, 13, 14]
  | .M => ![0, 4, 1, 2, 3, 8, 5, 6, 7, 12, 9, 10, 11, 14, 15, 16, 13, 17, 18, 19, 20]
  | .N => ![0, 4, 1, 2, 3, 8, 5, 6, 7, 10, 11, 12, 9, 14, 15, 16, 13, 17, 18, 19, 20]
  | .P => ![0, 4, 1, 2, 3, 8, 5, 6, 7, 10, 11, 12, 9, 14, 15, 16, 13, 17, 18, 19, 20, 21, 22]
  | .Q => ![0, 4, 1, 2, 3, 6, 7, 8, 5, 10, 11, 12, 9, 14, 15, 16, 13, 17, 18, 19, 20]
  | .R => ![0, 4, 1, 2, 3, 6, 7, 8, 5, 10, 11, 12, 9, 14, 15, 16, 13, 17, 18, 19, 20, 21, 22]
  | .S => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 10, 11, 12, 9, 14, 13, 15, 16, 17, 18]
  | .T => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 12, 9, 10, 11, 14, 13, 15, 16]
  | .U => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 12, 9, 10, 11, 14, 13, 15, 16, 17]
  | .V => ![0, 2, 3, 4, 1, 6, 7, 8, 5, 12, 9, 10, 11, 14, 13, 15, 16, 17, 18, 19, 20]

/-- The displayed row rotation has order dividing four. -/
theorem tableIGaloisNext_four (c : TableICase) :
    ∀ j, tableIGaloisNext c (tableIGaloisNext c
      (tableIGaloisNext c (tableIGaloisNext c j))) = j := by
  cases c <;> decide

/-- Galois row permutation, with inverse the third iterate. -/
def tableIGaloisPerm (c : TableICase) : Equiv.Perm (Fin (tableIRowCount c)) where
  toFun := tableIGaloisNext c
  invFun j := tableIGaloisNext c (tableIGaloisNext c (tableIGaloisNext c j))
  left_inv := tableIGaloisNext_four c
  right_inv := tableIGaloisNext_four c

/-- The permutation gives the exact column rotation from p. 374. -/
theorem tableIData_galois_entries (c : TableICase) (v : c.Variant) :
    ∀ j, (tableIData c v).dT j = (tableIData c v).dT (tableIGaloisNext c j) ∧
      ∀ i, (tableIData c v).iDz i j =
        (tableIData c v).iDz (galoisColumn i) (tableIGaloisNext c j) := by
  cases c <;> cases v <;> decide

/-- Galois symmetry holds on the full finite row type. -/
theorem tableIData_galoisSymmetry (c : TableICase) (v : c.Variant) :
    (tableIData c v).GaloisSymmetry :=
  ⟨tableIGaloisPerm c, tableIData_galois_entries c v⟩

/-- Each enumerated matrix satisfies the numerical hypotheses. This is a
verification of the catalogue, not an exhaustive classification theorem. -/
theorem tableIData_patternHypotheses (c : TableICase) (v : c.Variant) :
    (tableIData c v).TableIPatternHypotheses (tableIPrincipal c) where
  equation_3_2 := tableIData_equation3_2 c v
  equation_3_3 := tableIData_contributionBound c v
  equation_3_4 := tableIData_equation3_4 c v
  galois_symmetry := tableIData_galoisSymmetry c v
  principal_dT := congrFun (tableIMatrix_principal c v) 0
  principal_iDz := by
    intro i
    have h := congrFun (tableIMatrix_principal c v) i.succ
    fin_cases i <;> exact h
  z_nonzero := tableIData_z_nonzero c v


namespace TableICatalogue

/-- The literal case J on p. 375, including the printed `+2` at row 9,
column 0. This matrix fails (3.2); `rowsJ` has the required `−2` correction. -/
def rowsJPrinted : TableIMatrix (Fin 14) :=
  Fin.append z4 ![
    ![-1, 1, 0, 1, 0, 1],
    ![-1, 1, 1, 0, 1, 0],
    ![-1, 1, 2, 1, 2, 1],
    ![-1, 1, 1, 2, 1, 2],
    ![2, 2, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1]]

/-- The sole difference between the literal printing and the canonical J. -/
theorem rowsJPrinted_eq (j : Fin 14) (k : Fin 6) :
    rowsJPrinted j k = if j = 9 ∧ k = 0 then 2 else rowsJ j k := by
  fin_cases j <;> fin_cases k <;> decide

end TableICatalogue

/-- Exact transcription of all twenty-five printed matrices, including J's
inconsistent `+2`. Use `tableIMatrix` for the numerically consistent catalogue. -/
def tableIPrintedMatrix : (c : TableICase) → c.Variant → TableIMatrix (Fin (tableIRowCount c))
  | .J, _ => TableICatalogue.rowsJPrinted
  | c, v => tableIMatrix c v

/-- The literal printed columns as generalized decomposition data. -/
def tableIPrintedData (c : TableICase) (v : c.Variant) :
    GeneralizedDecompositionData (Fin (tableIRowCount c)) where
  dT j := tableIPrintedMatrix c v j 0
  iDz i j := tableIPrintedMatrix c v j i.succ

/-- Outside J, the printing and the canonical catalogue coincide. -/
theorem tableIPrintedMatrix_eq (c : TableICase) (v : c.Variant) (h : c ≠ .J) :
    tableIPrintedMatrix c v = tableIMatrix c v := by
  cases c <;> try rfl
  exact (h rfl).elim

/-- Outside J, the printed and canonical decomposition data coincide. -/
theorem tableIPrintedData_eq (c : TableICase) (v : c.Variant) (h : c ≠ .J) :
    tableIPrintedData c v = tableIData c v := by
  unfold tableIPrintedData tableIData
  rw [tableIPrintedMatrix_eq c v h]

/-- The printed `+2` in J makes the mixed inner product 8, not 0. -/
theorem tableIJPrinted_mixed_inner :
    columnInner (tableIPrintedData .J ()).dT ((tableIPrintedData .J ()).iDz 0) = 8 := by
  decide

/-- Precisely the printed J fails the Gram identities (3.2). -/
theorem tableIPrintedData_equation3_2_iff (c : TableICase) (v : c.Variant) :
    (tableIPrintedData c v).Equation3_2 ↔ c ≠ .J := by
  constructor
  · intro h hJ
    subst c
    cases v
    have ht := h.tz 0
    rw [tableIJPrinted_mixed_inner] at ht
    norm_num at ht
  · intro h
    rw [tableIPrintedData_eq c v h]
    exact tableIData_equation3_2 c v

/-- The principal row is also unchanged in the literal printing. -/
theorem tableIPrintedMatrix_principal (c : TableICase) (v : c.Variant) :
    tableIPrintedMatrix c v (tableIPrincipal c) = ![1, 1, 0, 0, 0, 0] := by
  cases c <;> cases v <;> decide

/-- The literal printing, including J, satisfies (3.3). -/
theorem tableIPrintedData_contributionBound (c : TableICase) (v : c.Variant) :
    (tableIPrintedData c v).ContributionBound := by
  by_cases h : c = .J
  · subst c
    cases v
    unfold ContributionBound
    decide
  · rw [tableIPrintedData_eq c v h]
    exact tableIData_contributionBound c v

/-- The literal printing, including J, satisfies (3.4). -/
theorem tableIPrintedData_equation3_4 (c : TableICase) (v : c.Variant) :
    (tableIPrintedData c v).Equation3_4 := by
  by_cases h : c = .J
  · subst c
    cases v
    unfold Equation3_4
    decide
  · rw [tableIPrintedData_eq c v h]
    exact tableIData_equation3_4 c v

end Stellmacher.Recognition.LyonsU3Four
