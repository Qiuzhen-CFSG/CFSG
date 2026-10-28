module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection
public import Stellmacher.Recognition.LyonsU3Four.TableILargeDifferenceGeometry
public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedMultiplicityAssembly

/-!
# Reduction of the large-difference cases of Table I

A Galois rotation places a magnitude-two entry in the first difference column.
The opposite entry vanishes by the Gram identities, and the remaining entries
sum to the negative of the first. The integer bounds therefore leave exactly
three signed shapes: `(2, -2, 0, 0)`, `(2, 0, 0, -2)`, and `(2, -1, 0, -1)`.

The first two shapes lead to the Z₁/Z₂ completion in cases A–E; the last leads
to Z₃ in cases F–G, allowing column reflection. The row-count identifications
remain separate obligations; the theorem below establishes their exhaustive
input split without presupposing any canonical identification.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 377–378,
Cases 1–4. The page image, including both orientations in Case 3, was checked.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- The Gram matrix and Galois action leave exactly three signed row shapes
at a large entry. No row-identification or catalogue assumption is used. -/
theorem large_difference_shapes (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (hl : d.HasLargeDifference) :
    d.HasPairedLargeDifferences ∨ d.HasIsolatedLargeDifference := by
  obtain ⟨j, hj⟩ := hl.at_zero d hg
  have hz : d.adjacentDifference 2 j = 0 := opposite_zero_of_large d h hg 0 j hj
  have hb := h.adjacentDifference_bounds d 1 j
  have hd := h.adjacentDifference_bounds d 3 j
  have hs := d.adjacentDifference_sum j
  simp [Fin.sum_univ_succ] at hs
  have ha : d.adjacentDifference 0 j = 2 ∨ d.adjacentDifference 0 j = -2 := by
    rcases lt_trichotomy (d.adjacentDifference 0 j) 0 with hn | he | hp
    · right; nlinarith
    · simp [he] at hj
    · left; nlinarith
  rcases ha with ha | ha
  · have hb' : d.adjacentDifference 1 j = -2 ∨ d.adjacentDifference 1 j = -1 ∨
        d.adjacentDifference 1 j = 0 := by omega
    rcases hb' with hb' | hb' | hb'
    · left
      refine ⟨j, 1, by norm_num, Or.inl ?_⟩
      have hd' : d.adjacentDifference 3 j = 0 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']
    · right
      refine ⟨j, 1, by norm_num, ?_⟩
      have hd' : d.adjacentDifference 3 j = -1 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']
    · left
      refine ⟨j, 1, by norm_num, Or.inr ?_⟩
      have hd' : d.adjacentDifference 3 j = -2 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']
  · have hb' : d.adjacentDifference 1 j = 2 ∨ d.adjacentDifference 1 j = 1 ∨
        d.adjacentDifference 1 j = 0 := by omega
    rcases hb' with hb' | hb' | hb'
    · left
      refine ⟨j, -1, by norm_num, Or.inl ?_⟩
      have hd' : d.adjacentDifference 3 j = 0 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']
    · right
      refine ⟨j, -1, by norm_num, ?_⟩
      have hd' : d.adjacentDifference 3 j = 1 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']
    · left
      refine ⟨j, -1, by norm_num, Or.inr ?_⟩
      have hd' : d.adjacentDifference 3 j = 2 := by omega
      funext i; fin_cases i <;> simp [ha, hb', hz, hd']

/-- The paired branch is complete. In the isolated branch the two remaining
finite enumeration contracts feed directly into the canonical row equivalence. -/
theorem hasCanonicalTableIPattern_or_reflect_of_largeDifference_enumeration
    (principal : I) (h : d.TableIPatternHypotheses principal)
    (hl : d.HasLargeDifference)
    (hcoverage : ∀ r, TableIIsolatedRows.Admissible r →
      ∃ a, r = TableIIsolatedRows.row a)
    (hcounts : ∀ n, TableIIsolatedRows.MultiplicityConditions n →
      ∃ c o, n = TableIIsolatedRows.solution c o) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal := by
  rcases d.large_difference_shapes h.equation_3_2 h.galois_symmetry hl with hp | hi
  · exact Or.inl (d.hasCanonicalTableIPattern_of_pairedLargeDifferences principal h hp)
  · have hc : ∀ j, ∃ a, d.normalizedTableIRow j = TableIIsolatedRows.row a :=
      fun j => hcoverage _ (d.isolated_normalized_admissible h hi j)
    exact d.hasCanonicalTableIPattern_or_reflect_of_isolated_solutions principal h hc
      (hcounts _ (d.isolated_multiplicity_conditions h hi hc))

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
