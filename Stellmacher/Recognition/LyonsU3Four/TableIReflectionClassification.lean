module

public import Stellmacher.Recognition.LyonsU3Four.TableICanonicalPatterns
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection
public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity

/-!
# Assembly for Table I classification up to reflection

Either orientation's normalized row counts give the corrected canonical
identification, including every duplicate and the principal row. The
independent enumeration branches in `tableI_difference_cases` must still
supply those counts or an equivalent signed identification. Reflection here
is numerical; it does not transport the section identity in a fixed basis.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
Table I pp. 374–377 and Cases 1–8, pp. 377–380.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- Either orientation's row multiplicities suffice for the corrected target. -/
theorem canonical_or_reflected_of_rowMultiplicity (principal : I)
    (h : d.TableIPatternHypotheses principal)
    (hm : (∃ (c : TableICase) (v : c.Variant), ∀ r,
      d.tableIRowMultiplicity r = Fintype.card {j // tableIMatrix c v j = r}) ∨
      (∃ (c : TableICase) (v : c.Variant), ∀ r,
      d.reflectColumns.tableIRowMultiplicity r =
        Fintype.card {j // tableIMatrix c v j = r})) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal := by
  rcases hm with ⟨c, v, hm⟩ | ⟨c, v, hm⟩
  · exact Or.inl (d.hasCanonicalTableIPattern_of_rowMultiplicity principal h c v hm)
  · exact Or.inr (d.reflectColumns.hasCanonicalTableIPattern_of_rowMultiplicity
      principal (h.reflectColumns d) c v hm)

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
