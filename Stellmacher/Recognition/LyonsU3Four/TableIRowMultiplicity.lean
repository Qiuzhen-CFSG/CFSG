module

public import Stellmacher.Recognition.LyonsU3Four.TableICanonicalPatterns
public import Mathlib.Data.Fintype.EquivFin

/-!
# Row multiplicities and principal-preserving signed identifications

Normalize each row by making its value at the involution positive. Equality
of the resulting row multiplicities with an explicit `tableIMatrix` gives a
signed row equivalence. A swap between equal rows makes this equivalence carry
the distinguished principal index to the printed principal index. Thus this
interface retains duplicates rather than identifying only the set of rows.

This module only assembles a canonical identification from supplied row counts.
The numerical enumeration establishing those counts is a separate obligation.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), Table I,
pp. 374–377 and its enumeration on pp. 377–380.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

variable {I : Type*} (d : GeneralizedDecompositionData I)

/-- The independent sign used to orient a row by its nonzero involution value. -/
def tableIRowSign (j : I) : ℤ := if 0 < d.zValue j then 1 else -1

theorem tableIRowSign_sq (j : I) : d.tableIRowSign j ^ 2 = 1 := by
  unfold tableIRowSign
  split <;> norm_num

/-- The row after the common sign of its six entries has been normalized. -/
def normalizedTableIRow (j : I) : TableIRow :=
  fun k => d.tableIRowSign j * d.tableIRow j k

variable [Fintype I]

theorem normalizedTableIRow_principal (principal : I)
    (h : d.TableIPatternHypotheses principal) :
    d.normalizedTableIRow principal = ![1, 1, 0, 0, 0, 0] := by
  have hz : d.zValue principal = 1 := by simp [zValue, h.principal_iDz]
  have hs : d.tableIRowSign principal = 1 := by
    simp [tableIRowSign, hz]
  funext k
  change d.tableIRowSign principal * d.tableIRow principal k = _
  rw [hs, one_mul, d.tableIRow_principal principal h]

/-- Count a normalized row with its full multiplicity. -/
def tableIRowMultiplicity (r : TableIRow) : ℕ :=
  Fintype.card {j // d.normalizedTableIRow j = r}

/-- Multiplicity equality with an explicit canonical matrix supplies the
required signed equivalence, including the principal row. -/
theorem hasCanonicalTableIPattern_of_rowMultiplicity (principal : I)
    (h : d.TableIPatternHypotheses principal) (c : TableICase) (v : c.Variant)
    (hm : ∀ r, d.tableIRowMultiplicity r =
      Fintype.card {j // tableIMatrix c v j = r}) :
    d.HasCanonicalTableIPattern principal := by
  classical
  let fibers (r : TableIRow) :
      {j // d.normalizedTableIRow j = r} ≃ {j // tableIMatrix c v j = r} :=
    Fintype.equivOfCardEq (hm r)
  let e : I ≃ Fin (tableIRowCount c) := Equiv.ofFiberEquiv fibers
  have he (j : I) : tableIMatrix c v (e j) = d.normalizedTableIRow j :=
    Equiv.ofFiberEquiv_map fibers j
  have hp : tableIMatrix c v (e principal) =
      tableIMatrix c v (tableIPrincipal c) := by
    rw [he, d.normalizedTableIRow_principal principal h, tableIMatrix_principal]
  let e' := e.trans (Equiv.swap (e principal) (tableIPrincipal c))
  refine ⟨c, v, e', d.tableIRowSign, d.tableIRowSign_sq, ?_, ?_⟩
  · intro j k
    have hs := congrFun (Equiv.apply_swap_eq_self hp (e j)) k
    change d.tableIRow j k = d.tableIRowSign j *
      tableIMatrix c v (Equiv.swap (e principal) (tableIPrincipal c) (e j)) k
    rw [hs, he]
    change d.tableIRow j k = d.tableIRowSign j *
      (d.tableIRowSign j * d.tableIRow j k)
    rw [← mul_assoc, ← pow_two, tableIRowSign_sq, one_mul]
  · exact Equiv.swap_apply_left _ _


end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
