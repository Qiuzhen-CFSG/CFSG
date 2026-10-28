module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.SourceCubic.MatrixBlocks

/-!
# Comparing the literal E cubic with its pair model

The comparison is unconditional whenever one input lies on the matrix axis.
The trace calculation gives coefficient four on a triangle; the actual
short tensors and orthogonality give minus eight on the mixed same-pair
triple and zero on every other matrix-containing triple. Symmetry supplies
all placements of these source blocks.

The final assembly theorem takes only the remaining all-short product table
as an explicit premise. It does not yet establish the unconditional complete
restriction: that premise must be discharged by multiplication of the actual
pure-four extraspecial words. The model form is never substituted for the
existing Griess form.

Source: Aschbacher, *Sporadic Groups*, 27.8, 28.2, 28.4, 28.7 and 29.11,
printed pp. 150–152, 159–160 (PDF pages 81–82, 85–86).
-/

@[expose] public section
open scoped BigOperators Matrix
namespace Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
noncomputable section
open LocalC ShortFamilies Griess TrialitySpin Atlas.Codes
open TrialitySpin.SignedModules.Natural

/-- The full literal comparison for every triple containing a matrix-axis
vector. This includes all matrix, mixed, and two-axis zero placements. -/
theorem literalPair_beta_of_zero_axis
    (i j k : Axis) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q)
    (hzero : i = 0 ∨ j = 0 ∨ k = 0) :
    griessBeta (eInclusion (literalPair i x y hxy))
      (eInclusion (literalPair j u v huv)) (eInclusion (literalPair k p q hpq)) =
    pairBeta (pairVector i x y hxy) (pairVector j u v huv) (pairVector k p q hpq) := by
  rw [pairBeta_table, literalPair_inclusion, literalPair_inclusion, literalPair_inclusion]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> dsimp only
  · -- Axes (0, 0, 0)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSS]
    simpa using symmetricPair_beta x y u v p q
  · -- Axes (0, 0, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (0, 0, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (0, 1, 0)
    rw [griessBeta_swap_right]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (0, 1, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false u v huv) (shortPair false p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (0, 1, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false u v huv) (shortPair true p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (0, 2, 0)
    rw [griessBeta_swap_right]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (0, 2, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true u v huv) (shortPair false p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (0, 2, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true u v huv) (shortPair true p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (1, 0, 0)
    rw [griessBeta_swap_left]
    rw [griessBeta_swap_right]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (1, 0, 1)
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false x y hxy) (shortPair false p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (1, 0, 2)
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false x y hxy) (shortPair true p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
    all_goals split_ifs
    all_goals grind
  · -- Axes (1, 1, 0)
    rw [griessBeta_swap_right]
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false x y hxy) (shortPair false u v huv) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · simp at hzero
  · simp at hzero
  · -- Axes (1, 2, 0)
    rw [griessBeta_swap_right]
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair false x y hxy) (shortPair true u v huv) = _
    rw [srr_shortPair] <;> try assumption
    simp
    all_goals split_ifs
    all_goals grind
  · simp at hzero
  · simp at hzero
  · -- Axes (2, 0, 0)
    rw [griessBeta_swap_left]
    rw [griessBeta_swap_right]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SSR]
    simp
  · -- Axes (2, 0, 1)
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true x y hxy) (shortPair false p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
    all_goals split_ifs
    all_goals grind
  · -- Axes (2, 0, 2)
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true x y hxy) (shortPair true p q hpq) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · -- Axes (2, 1, 0)
    rw [griessBeta_swap_right]
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true x y hxy) (shortPair false u v huv) = _
    rw [srr_shortPair] <;> try assumption
    simp
    all_goals split_ifs
    all_goals grind
  · simp at hzero
  · simp at hzero
  · -- Axes (2, 2, 0)
    rw [griessBeta_swap_right]
    rw [griessBeta_swap_left]
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_SRR]
    change sourceSRR sourceLatticeComparison _ (shortPair true x y hxy) (shortPair true u v huv) = _
    rw [srr_shortPair] <;> try assumption
    simp
  · simp at hzero
  · simp at hzero

/-- Assembly of the literal cubic from the all-short calculation. The matrix
and mixed coefficients are proved here; the hypothesis is precisely the
remaining extraspecial product calculation, not an invariant-form premise. -/
theorem literalPair_beta_of_shortTable
    (hshort : ∀ (b c d : Bool) (x y u v p q : Omega)
      (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q),
      shortCubic sourceLatticeComparison (shortPair b x y hxy)
        (shortPair c u v huv) (shortPair d p q hpq) =
        if b = c ∧ c = d then 4 * triangle x y u v p q else 0)
    (i j k : Axis) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    griessBeta (eInclusion (literalPair i x y hxy))
      (eInclusion (literalPair j u v huv)) (eInclusion (literalPair k p q hpq)) =
    pairBeta (pairVector i x y hxy) (pairVector j u v huv) (pairVector k p q hpq) := by
  by_cases hz : i = 0 ∨ j = 0 ∨ k = 0
  · exact literalPair_beta_of_zero_axis i j k x y u v p q hxy huv hpq hz
  have axes (a : Axis) (ha : a ≠ 0) : a = 1 ∨ a = 2 := by
    fin_cases a
    · exact (ha rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hi : i ≠ 0 := fun h => hz (Or.inl h)
  have hj : j ≠ 0 := fun h => hz (Or.inr (Or.inl h))
  have hk : k ≠ 0 := fun h => hz (Or.inr (Or.inr h))
  rw [pairBeta_table, literalPair_inclusion, literalPair_inclusion, literalPair_inclusion]
  rcases axes i hi with rfl | rfl <;> rcases axes j hj with rfl | rfl <;>
    rcases axes k hk with rfl | rfl <;> dsimp only
  · -- Axes (1, 1, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair false x y hxy) (shortPair false u v huv) (shortPair false p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (1, 1, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair false x y hxy) (shortPair false u v huv) (shortPair true p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (1, 2, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair false x y hxy) (shortPair true u v huv) (shortPair false p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (1, 2, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair false x y hxy) (shortPair true u v huv) (shortPair true p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (2, 1, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair true x y hxy) (shortPair false u v huv) (shortPair false p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (2, 1, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair true x y hxy) (shortPair false u v huv) (shortPair true p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (2, 2, 1)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair true x y hxy) (shortPair true u v huv) (shortPair false p q hpq) = _
    rw [hshort]
    simp
  · -- Axes (2, 2, 2)
    change sourceBeta sourceLatticeComparison _ _ _ = _
    rw [sourceBeta_RRR]
    change shortCubic sourceLatticeComparison
      (shortPair true x y hxy) (shortPair true u v huv) (shortPair true p q hpq) = _
    rw [hshort]
    simp

end
end Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
