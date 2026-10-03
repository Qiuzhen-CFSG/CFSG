module

public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices

/-!
# Canonical Table I patterns and an orientation obstruction

`HasCanonicalTableIPattern` requires a signed row equivalence with one of the
explicit matrices, including all row multiplicities and the principal index.
Unlike `TableIPattern`, it does not permit a freely chosen matrix.

The numerical `TableIPatternHypotheses` do not imply this relation for the
current catalogue. Reflect the last four columns of F by interchanging the
second and third involution columns and the fourth and fifth. The resulting
matrix still satisfies every hypothesis, with the inverse Galois permutation.
Its row `[1, 1, 0, 2, 1, 1]` occurs in no canonical matrix, even up to sign.
Finite checks prove these assertions, and the obstruction to any signed row
equivalence follows by considering this one row.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I, pp. 374–377, and Case 3 on p. 378. The printed Z₃
on p. 377 has one orientation. Case 3 discusses both `(1, 2, 0, 1, 1)` and
`(1, 0, 2, 1, 1)` as involution rows but develops only the first. The checked
obstruction below concerns exactly the fixed-column catalogue; it does not
assert that no enlarged catalogue or column-permutation formulation works.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

namespace GeneralizedDecompositionData

/-- Identification with the actual canonical catalogue, retaining repeated
rows and sending the distinguished principal index to the printed one. -/
def HasCanonicalTableIPattern {I : Type*}
    (d : GeneralizedDecompositionData I) (principal : I) : Prop :=
  ∃ (c : TableICase) (v : c.Variant)
    (e : I ≃ Fin (tableIRowCount c)) (ε : I → ℤ),
    (∀ j, ε j ^ 2 = 1) ∧
    (∀ j k, d.tableIRow j k = ε j * tableIMatrix c v (e j) k) ∧
    e principal = tableIPrincipal c

end GeneralizedDecompositionData

/-- Every catalogue member has its tautological canonical identification. -/
theorem tableIData_hasCanonicalTableIPattern (c : TableICase) (v : c.Variant) :
    (tableIData c v).HasCanonicalTableIPattern (tableIPrincipal c) := by
  refine ⟨c, v, Equiv.refl _, fun _ => 1, ?_, ?_, rfl⟩
  · intro j
    norm_num
  · intro j k
    simp

namespace TableICanonicalObstruction

/-- Reflect F's last four columns. This preserves all numerical hypotheses
but is not represented by the current fixed-column catalogue. -/
def reflectedF : GeneralizedDecompositionData (Fin 15) where
  dT := (tableIData .F ()).dT
  iDz i j := (tableIData .F ()).iDz (![0, 2, 1, 4, 3] i) j

/-- The reflected matrix satisfies the exact hypotheses of the requested
classification, including nonvanishing and the distinguished principal row. -/
theorem reflectedF_patternHypotheses : reflectedF.TableIPatternHypotheses 0 where
  equation_3_2 := by constructor <;> decide
  equation_3_3 := by unfold ContributionBound; decide
  equation_3_4 := by unfold Equation3_4; decide
  galois_symmetry := by
    refine ⟨(tableIGaloisPerm .F).symm, ?_⟩
    decide
  principal_dT := by decide
  principal_iDz := by decide
  z_nonzero := by decide

/-- The row detecting the missing orientation. -/
theorem reflectedF_row_one :
    reflectedF.tableIRow 1 = ![1, 1, 0, 2, 1, 1] := by decide

/-- Neither sign of the detecting row occurs in any canonical matrix. -/
theorem reflectedF_row_one_absent (c : TableICase) (v : c.Variant) :
    ∀ j, (¬ ∀ k, reflectedF.tableIRow 1 k = tableIMatrix c v j k) ∧
      (¬ ∀ k, reflectedF.tableIRow 1 k = -tableIMatrix c v j k) := by
  cases c <;> cases v <;> decide

/-- No row permutation and independent row signs identify reflected F with
any canonical matrix, even without imposing the principal-index condition. -/
theorem reflectedF_no_signed_identification (c : TableICase) (v : c.Variant)
    (f : Fin 15 → Fin (tableIRowCount c)) (ε : Fin 15 → ℤ)
    (hε : ∀ j, ε j ^ 2 = 1) :
    ¬ ∀ j k, reflectedF.tableIRow j k = ε j * tableIMatrix c v (f j) k := by
  intro hi
  rcases sq_eq_one_iff.mp (hε 1) with h | h
  · exact (reflectedF_row_one_absent c v (f 1)).1
      (by simpa only [h, one_mul] using hi 1)
  · exact (reflectedF_row_one_absent c v (f 1)).2
      (by simpa only [h, neg_one_mul] using hi 1)

/-- A counterexample to classification into the fixed canonical catalogue. -/
theorem reflectedF_not_canonical : ¬ reflectedF.HasCanonicalTableIPattern 0 := by
  rintro ⟨c, v, e, ε, hε, hi, _⟩
  exact reflectedF_no_signed_identification c v e ε hε hi

/-- The proposed implication is false already for fifteen rows. Any repair
must address the catalogue or the allowed column identifications. -/
theorem patternHypotheses_not_sufficient :
    ¬ (∀ (d : GeneralizedDecompositionData (Fin 15)) (principal : Fin 15),
      d.TableIPatternHypotheses principal → d.HasCanonicalTableIPattern principal) := by
  intro h
  exact reflectedF_not_canonical (h reflectedF 0 reflectedF_patternHypotheses)

end TableICanonicalObstruction
end Stellmacher.Recognition.LyonsU3Four
