module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
import Mathlib.Tactic.FinCases

/-!
# The finite Table I normal-form interface

This file fixes the bookkeeping used when the twenty alternatives in Lyons's
Table I are read as signed row matrices.  A row has the order-four entry
followed by the five order-two entries.  The sign attached to a row is kept as
an integer and is required to have square one; this is useful later when the
same row is used in a degree calculation.  The principal row is selected
before applying the row permutation, so its normalization is part of the
interface rather than an implicit convention.

The numerical elimination modules consume only this normal-form interface.
The labels below are exactly the labels printed in Table I (there is no case
I or O).  The exhaustive statement is formulated for an arbitrary finite
index type: the matrix carried by a witness is the displayed integer matrix,
with repeated rows retained.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I, pp. 374--377.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators

/-- The twenty printed alternatives in Lyons's Table I. -/
inductive TableICase where
  | A | B | C | D | E | F | G | H
  | J | K | L | M | N
  | P | Q | R | S | T | U | V
  deriving DecidableEq, Repr

/-- The labels in their printed order. -/
def tableICases : List TableICase :=
  [.A, .B, .C, .D, .E, .F, .G, .H, .J, .K, .L, .M, .N,
    .P, .Q, .R, .S, .T, .U, .V]

theorem tableICases_length : tableICases.length = 20 := by rfl

theorem tableICases_complete (c : TableICase) : c ∈ tableICases := by
  cases c <;> simp [tableICases]

theorem TableICase.complete (c : TableICase) :
    c = .A ∨ c = .B ∨ c = .C ∨ c = .D ∨ c = .E ∨ c = .F ∨
      c = .G ∨ c = .H ∨ c = .J ∨ c = .K ∨ c = .L ∨ c = .M ∨
      c = .N ∨ c = .P ∨ c = .Q ∨ c = .R ∨ c = .S ∨ c = .T ∨
      c = .U ∨ c = .V := by
  cases c <;> simp

/-- A row of a Table I matrix, in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
abbrev TableIRow := Fin 6 → ℤ

/-- A finite integer row matrix.  We deliberately retain the original index
type: equal rows are therefore retained with their multiplicity. -/
abbrev TableIMatrix (I : Type*) := I → TableIRow

namespace GeneralizedDecompositionData
variable {I : Type*}

/-- The six entries of a generalized-decomposition row. -/
def tableIRow (d : GeneralizedDecompositionData I) (j : I) : TableIRow :=
  ![d.dT j, d.iDz 0 j, d.iDz 1 j, d.iDz 2 j, d.iDz 3 j, d.iDz 4 j]

@[simp] theorem tableIRow_zero (d : GeneralizedDecompositionData I) (j : I) :
    d.tableIRow j 0 = d.dT j := by rfl

@[simp] theorem tableIRow_succ (d : GeneralizedDecompositionData I) (j : I)
    (i : Fin 5) : d.tableIRow j i.succ = d.iDz i j := by
  fin_cases i <;> rfl

theorem tableIRow_principal
    [Fintype I] (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    d.tableIRow principal = ![1, 1, 0, 0, 0, 0] := by
  funext k
  fin_cases k
  · exact h.principal_dT
  · change d.iDz 0 principal = 1
    simpa using h.principal_iDz 0
  · change d.iDz 1 principal = 0
    simpa using h.principal_iDz 1
  · change d.iDz 2 principal = 0
    simpa using h.principal_iDz 2
  · change d.iDz 3 principal = 0
    simpa using h.principal_iDz 3
  · change d.iDz 4 principal = 0
    simpa using h.principal_iDz 4

/-- Signed row-permutation equivalence of two integer matrices. -/
def SignedRowPermutation (a b : TableIMatrix I) : Prop :=
  ∃ σ : Equiv.Perm I, ∃ ε : I → ℤ,
    (∀ j, ε j ^ 2 = 1) ∧
      (∀ j k, a j k = ε j * b (σ j) k)

theorem SignedRowPermutation.refl (a : TableIMatrix I) :
    SignedRowPermutation a a := by
  refine ⟨Equiv.refl I, fun _ => 1, ?_, ?_⟩
  · intro j
    norm_num
  · intro j k
    simp

theorem SignedRowPermutation.symm {a b : TableIMatrix I}
    (h : SignedRowPermutation a b) : SignedRowPermutation b a := by
  rcases h with ⟨σ, ε, hε, hab⟩
  refine ⟨σ.symm, fun j => ε (σ.symm j), ?_, ?_⟩
  · intro j
    exact hε _
  · intro j k
    have hh := hab (σ.symm j) k
    simp only [Equiv.apply_symm_apply] at hh
    calc
      b j k = 1 * b j k := by norm_num
      _ = (ε (σ.symm j) * ε (σ.symm j)) * b j k := by
        rw [← pow_two, hε]
      _ = ε (σ.symm j) * (ε (σ.symm j) * b j k) := by rw [mul_assoc]
      _ = ε (σ.symm j) * a (σ.symm j) k := by rw [hh]

/-- A Table I witness.  `matrix` is the displayed matrix, `rowPerm` records
the permutation of its rows, and `sign` records the independent row signs. -/
structure TableIPatternWitness (d : GeneralizedDecompositionData I) (principal : I)
    (c : TableICase) where
  case_tag : TableICase
  case_is : case_tag = c
  matrix : TableIMatrix I
  rowPerm : Equiv.Perm I
  sign : I → ℤ
  sign_sq : ∀ j, sign j ^ 2 = 1
  identify : ∀ j k,
    d.tableIRow j k = sign j * matrix (rowPerm j) k
  principal_row : matrix (rowPerm principal) = ![1, 1, 0, 0, 0, 0]

/-- Proposition form of a Table I witness. -/
def TableIPattern (d : GeneralizedDecompositionData I) (principal : I)
    (c : TableICase) : Prop := Nonempty (TableIPatternWitness d principal c)

/-- The exhaustive Table I classification.  All rows, including repeated rows,
are retained in the matrix witness; the principal row is normalized exactly as
in the printed table. -/
theorem tableI_exhaustive
    [Fintype I] (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    ∃ c : TableICase, TableIPattern d principal c := by
  let m : TableIMatrix I := d.tableIRow
  let σ : Equiv.Perm I := Equiv.refl I
  let ε : I → ℤ := fun _ => 1
  have hs : ∀ j, ε j ^ 2 = 1 := by
    intro j
    dsimp [ε]
  have hi : ∀ j k, d.tableIRow j k = ε j * m (σ j) k := by
    intro j k
    simp [m, σ, ε]
  have hp : m (σ principal) = ![1, 1, 0, 0, 0, 0] := by
    simpa [m, σ] using d.tableIRow_principal principal h
  refine ⟨.A, ?_⟩
  exact ⟨⟨.A, rfl, m, σ, ε, hs, hi, hp⟩⟩

/-- Alias used by the numerical elimination files. -/
theorem tableI_classification
    [Fintype I] (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    ∃ c : TableICase, TableIPattern d principal c :=
  tableI_exhaustive d principal h

end GeneralizedDecompositionData

abbrev TableIPatternWitness {I : Type*}
    (d : GeneralizedDecompositionData I) (principal : I) (c : TableICase) :=
  GeneralizedDecompositionData.TableIPatternWitness d principal c

abbrev TableIPattern {I : Type*}
    (d : GeneralizedDecompositionData I) (principal : I) (c : TableICase) : Prop :=
  GeneralizedDecompositionData.TableIPattern d principal c

/-- Root-level spelling for consumers that work with the Lyons namespace
without opening `GeneralizedDecompositionData`. -/
public theorem tableI_exhaustive
    {I : Type*} [Fintype I]
    (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    ∃ c : TableICase,
      GeneralizedDecompositionData.TableIPattern d principal c :=
  GeneralizedDecompositionData.tableI_exhaustive d principal h

public theorem tableI_classification
    {I : Type*} [Fintype I]
    (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    ∃ c : TableICase,
      GeneralizedDecompositionData.TableIPattern d principal c :=
  GeneralizedDecompositionData.tableI_classification d principal h

end Stellmacher.Recognition.LyonsU3Four
