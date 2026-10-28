module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections.Parameters
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords

/-!
# Split-root supports for the six Ree sections

The explicit supports use the 24 literal roots of `LongCommutators.RootCalculus`.
Their generated split subgroups contain the corresponding fixed-group joins.
If collection in those supports is available, uniqueness of the existing full
positive coordinates forces the required vanishing of the Ree parameters.
Thus the only remaining input is collection in these smaller split supports;
no fixed-point cardinality or elementary-rank assertion is assumed.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations.Sections
open Subgroup Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination

/-- Omitted split-root slots, in the literal 24-root numbering. -/
def omitted : Kind → List (Fin 24)
  | .d => [0, 1, 18, 19, 22, 23]
  | .d1 => [0, 1, 16, 17, 18, 19, 20, 21, 22, 23]
  | .d2 => [0, 1, 2, 3, 4, 5, 18, 19, 22, 23]
  | .t1 => [0, 1, 6, 7, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23]
  | .t2 => [0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 18, 19, 22, 23]
  | .k => [0, 1, 18, 19, 20, 21, 22, 23]

def Allowed (s : Kind) (i : Fin 24) : Prop := i ∉ omitted s
instance (s : Kind) (i : Fin 24) : Decidable (Allowed s i) :=
  inferInstanceAs (Decidable (i ∉ omitted s))

/-- Generated split subgroup; these roots are actual Chevalley matrices. -/
def splitSection (m : ℕ) (s : Kind) : Subgroup (SplitGroup m) :=
  closure {x | ∃ i : Fin 24, Allowed s i ∧ ∃ a : CoefficientField m,
    MatrixRelations.LongCommutators.X m i a = x}

/-- The collection input concerns only split-root words, before taking fixed points. -/
def SplitCollection (m : ℕ) : Prop :=
  ∀ s : Kind, ∀ x ∈ splitSection m s, ∃ v : Fin 24 → CoefficientField m,
    (∀ i, ¬ Allowed s i → v i = 0) ∧ splitWord m v = x

theorem factor_mem (m : ℕ) (s : Kind) (i : Fin 24) (hi : Allowed s i)
    (a : CoefficientField m) :
    MatrixRelations.LongCommutators.X m i a ∈ splitSection m s :=
  subset_closure ⟨i, hi, a, rfl⟩

private def mainSlots : Fin 8 → List (Fin 24)
  | 0 => [0, 1, 2]
  | 1 => [4, 5]
  | 2 => [6, 7, 8]
  | 3 => [10, 11]
  | 4 => [12, 13, 14]
  | 5 => [16, 17]
  | 6 => [18, 19, 20]
  | 7 => [22, 23]

private theorem mainWord_mem (m : ℕ) (s : Kind) (i : Fin 8)
    (hi : ∀ j ∈ mainSlots i, Allowed s j) (a : CoefficientField m) :
    rootWord m i a ∈ splitSection m s := by
  fin_cases i
  · change (MatrixRelations.LongCommutators.X m 0 a *
      MatrixRelations.LongCommutators.X m 1 (rootFieldEnd m (longRoot 0) a)) *
      MatrixRelations.LongCommutators.X m 2 (a * rootFieldEnd m (longRoot 0) a) ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 0 (hi 0 (by decide)) _)
        (factor_mem m s 1 (hi 1 (by decide)) _))
      (factor_mem m s 2 (hi 2 (by decide)) _)
  · change (MatrixRelations.LongCommutators.X m 4 a *
      MatrixRelations.LongCommutators.X m 5 (rootFieldEnd m (longRoot 1) a)) *
      1 ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 4 (hi 4 (by decide)) _)
        (factor_mem m s 5 (hi 5 (by decide)) _))
      (one_mem _)
  · change (MatrixRelations.LongCommutators.X m 6 a *
      MatrixRelations.LongCommutators.X m 7 (rootFieldEnd m (longRoot 2) a)) *
      MatrixRelations.LongCommutators.X m 8 (a * rootFieldEnd m (longRoot 2) a) ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 6 (hi 6 (by decide)) _)
        (factor_mem m s 7 (hi 7 (by decide)) _))
      (factor_mem m s 8 (hi 8 (by decide)) _)
  · change (MatrixRelations.LongCommutators.X m 10 a *
      MatrixRelations.LongCommutators.X m 11 (rootFieldEnd m (longRoot 3) a)) *
      1 ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 10 (hi 10 (by decide)) _)
        (factor_mem m s 11 (hi 11 (by decide)) _))
      (one_mem _)
  · change (MatrixRelations.LongCommutators.X m 12 a *
      MatrixRelations.LongCommutators.X m 13 (rootFieldEnd m (longRoot 4) a)) *
      MatrixRelations.LongCommutators.X m 14 (a * rootFieldEnd m (longRoot 4) a) ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 12 (hi 12 (by decide)) _)
        (factor_mem m s 13 (hi 13 (by decide)) _))
      (factor_mem m s 14 (hi 14 (by decide)) _)
  · change (MatrixRelations.LongCommutators.X m 16 a *
      MatrixRelations.LongCommutators.X m 17 (rootFieldEnd m (longRoot 5) a)) *
      1 ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 16 (hi 16 (by decide)) _)
        (factor_mem m s 17 (hi 17 (by decide)) _))
      (one_mem _)
  · change (MatrixRelations.LongCommutators.X m 18 a *
      MatrixRelations.LongCommutators.X m 19 (rootFieldEnd m (longRoot 6) a)) *
      MatrixRelations.LongCommutators.X m 20 (a * rootFieldEnd m (longRoot 6) a) ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 18 (hi 18 (by decide)) _)
        (factor_mem m s 19 (hi 19 (by decide)) _))
      (factor_mem m s 20 (hi 20 (by decide)) _)
  · change (MatrixRelations.LongCommutators.X m 22 a *
      MatrixRelations.LongCommutators.X m 23 (rootFieldEnd m (longRoot 7) a)) *
      1 ∈ splitSection m s
    exact (splitSection m s).mul_mem
      ((splitSection m s).mul_mem
        (factor_mem m s 22 (hi 22 (by decide)) _)
        (factor_mem m s 23 (hi 23 (by decide)) _))
      (one_mem _)

private def evenIndex : Fin 4 → Fin 8 := ![0, 2, 4, 6]
private def centralSlots : Fin 4 → List (Fin 24)
  | 0 => [2, 3]
  | 1 => [8, 9]
  | 2 => [14, 15]
  | 3 => [20, 21]

private theorem centralWord_mem (m : ℕ) (s : Kind) (i : Fin 4)
    (hi : ∀ j ∈ centralSlots i, Allowed s j) (a : CoefficientField m) :
    centralWord m (evenIndex i) a ∈ splitSection m s := by
  fin_cases i
  · change MatrixRelations.LongCommutators.X m 3 a *
      MatrixRelations.LongCommutators.X m 2 (rootFieldEnd m (longRoot 0) a) ∈ _
    exact (splitSection m s).mul_mem
      (factor_mem m s 3 (hi 3 (by decide)) _)
      (factor_mem m s 2 (hi 2 (by decide)) _)
  · change MatrixRelations.LongCommutators.X m 9 a *
      MatrixRelations.LongCommutators.X m 8 (rootFieldEnd m (longRoot 2) a) ∈ _
    exact (splitSection m s).mul_mem
      (factor_mem m s 9 (hi 9 (by decide)) _)
      (factor_mem m s 8 (hi 8 (by decide)) _)
  · change MatrixRelations.LongCommutators.X m 15 a *
      MatrixRelations.LongCommutators.X m 14 (rootFieldEnd m (longRoot 4) a) ∈ _
    exact (splitSection m s).mul_mem
      (factor_mem m s 15 (hi 15 (by decide)) _)
      (factor_mem m s 14 (hi 14 (by decide)) _)
  · change MatrixRelations.LongCommutators.X m 21 a *
      MatrixRelations.LongCommutators.X m 20 (rootFieldEnd m (longRoot 6) a) ∈ _
    exact (splitSection m s).mul_mem
      (factor_mem m s 21 (hi 21 (by decide)) _)
      (factor_mem m s 20 (hi 20 (by decide)) _)

private theorem main_le (m : ℕ) (s : Kind) (i : Fin 8)
    (hi : ∀ j ∈ mainSlots i, Allowed s j) :
    X m i ≤ (splitSection m s).comap (toSplitGroup m) := by
  apply (closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  change toSplitGroup m (mainElement m i a) ∈ splitSection m s
  rw [mainElement_coe]
  exact mainWord_mem m s i hi a

private theorem central_le (m : ℕ) (s : Kind) (i : Fin 4)
    (hi : ∀ j ∈ centralSlots i, Allowed s j) :
    Y m (evenIndex i) ≤ (splitSection m s).comap (toSplitGroup m) := by
  apply (closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  change toSplitGroup m (centralElement m (evenIndex i) a) ∈ splitSection m s
  rw [centralElement_coe]
  exact centralWord_mem m s i hi a

/-- The literal subgroup generators use only the displayed split roots. -/
theorem section_le_split (m : ℕ) (s : Kind) :
    subgroup m s ≤ (splitSection m s).comap (toSplitGroup m) := by
  cases s <;> simp only [subgroup, D, D₁, D₂, T₁, T₂, K, left, right,
    middle, middleCenter]
  · exact (sup_le (sup_le (sup_le (central_le m .d 0 (by decide)) (main_le m .d 1 (by decide))) (sup_le (sup_le (main_le m .d 2 (by decide)) (main_le m .d 3 (by decide))) (main_le m .d 4 (by decide)))) (sup_le (main_le m .d 5 (by decide)) (central_le m .d 3 (by decide))))
  · exact (sup_le (sup_le (central_le m .d1 0 (by decide)) (main_le m .d1 1 (by decide))) (sup_le (sup_le (main_le m .d1 2 (by decide)) (main_le m .d1 3 (by decide))) (main_le m .d1 4 (by decide))))
  · exact (sup_le (sup_le (sup_le (main_le m .d2 2 (by decide)) (main_le m .d2 3 (by decide))) (main_le m .d2 4 (by decide))) (sup_le (main_le m .d2 5 (by decide)) (central_le m .d2 3 (by decide))))
  · exact (sup_le (sup_le (central_le m .t1 0 (by decide)) (main_le m .t1 1 (by decide))) (sup_le (sup_le (central_le m .t1 1 (by decide)) (main_le m .t1 3 (by decide))) (central_le m .t1 2 (by decide))))
  · exact (sup_le (sup_le (sup_le (central_le m .t2 1 (by decide)) (main_le m .t2 3 (by decide))) (central_le m .t2 2 (by decide))) (sup_le (main_le m .t2 5 (by decide)) (central_le m .t2 3 (by decide))))
  · exact (sup_le (sup_le (sup_le (central_le m .k 0 (by decide)) (main_le m .k 1 (by decide))) (sup_le (sup_le (main_le m .k 2 (by decide)) (main_le m .k 3 (by decide))) (main_le m .k 4 (by decide)))) (main_le m .k 5 (by decide)))

private theorem section_le_unipotent (m : ℕ) (s : Kind) :
    subgroup m s ≤ unipotent m := by
  cases s <;> simp only [subgroup, D, D₁, D₂, T₁, T₂, K, left, right,
    middle, middleCenter]
  · exact (sup_le (sup_le (sup_le (Y_le_unipotent m 0) (X_le_unipotent m 1)) (sup_le (sup_le (X_le_unipotent m 2) (X_le_unipotent m 3)) (X_le_unipotent m 4))) (sup_le (X_le_unipotent m 5) (Y_le_unipotent m 6)))
  · exact (sup_le (sup_le (Y_le_unipotent m 0) (X_le_unipotent m 1)) (sup_le (sup_le (X_le_unipotent m 2) (X_le_unipotent m 3)) (X_le_unipotent m 4)))
  · exact (sup_le (sup_le (sup_le (X_le_unipotent m 2) (X_le_unipotent m 3)) (X_le_unipotent m 4)) (sup_le (X_le_unipotent m 5) (Y_le_unipotent m 6)))
  · exact (sup_le (sup_le (Y_le_unipotent m 0) (X_le_unipotent m 1)) (sup_le (sup_le (Y_le_unipotent m 2) (X_le_unipotent m 3)) (Y_le_unipotent m 4)))
  · exact (sup_le (sup_le (sup_le (Y_le_unipotent m 2) (X_le_unipotent m 3)) (Y_le_unipotent m 4)) (sup_le (X_le_unipotent m 5) (Y_le_unipotent m 6)))
  · exact (sup_le (sup_le (sup_le (Y_le_unipotent m 0) (X_le_unipotent m 1)) (sup_le (sup_le (X_le_unipotent m 2) (X_le_unipotent m 3)) (X_le_unipotent m 4))) (X_le_unipotent m 5))

/-- Split-root vanishing detects precisely the required Ree-coordinate support. -/
theorem supported_of_split (m : ℕ) (s : Kind) (p : PositiveParameters m)
    (h : ∀ i, ¬ Allowed s i → parameters m p i = 0) : Supported s p := by
  cases s with
  | d => exact ⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩
  | d1 => exact ⟨⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩, (h 16 (by decide)), (h 21 (by decide))⟩
  | d2 => exact ⟨⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩, (h 4 (by decide)), (h 3 (by decide))⟩
  | t1 => exact ⟨⟨⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩, (h 16 (by decide)), (h 21 (by decide))⟩, (h 12 (by decide)), (h 6 (by decide))⟩
  | t2 => exact ⟨⟨⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩, (h 4 (by decide)), (h 3 (by decide))⟩, (h 12 (by decide)), (h 6 (by decide))⟩
  | k => exact ⟨⟨(h 22 (by decide)), (h 0 (by decide)), (h 18 (by decide))⟩, (h 21 (by decide))⟩

/-- Collection plus existing positive-coordinate uniqueness gives the actual
supported factorization of every element of each literal fixed-group join. -/
theorem factorization_of_splitCollection (m : ℕ) (h : SplitCollection m)
    (s : Kind) (x : Model m) (hx : x ∈ subgroup m s) :
    ∃ p : PositiveParameters m, Supported s p ∧ wordElement m p = x := by
  obtain ⟨p, hp⟩ := exists_positiveWord m x (section_le_unipotent m s hx)
  obtain ⟨v, hv, he⟩ := h s (toSplitGroup m x) (section_le_split m s hx)
  have hvp : parameters m p = v := by
    apply splitWord_injective m
    rw [← positiveWord_split, ← hp, he]
  refine ⟨p, supported_of_split m s p ?_, ?_⟩
  · simpa only [hvp] using hv
  · apply toSplitGroup_injective m
    rw [wordElement_coe, hp]

end ReeF4.ElementaryTwoBound.RootCalculations.Sections
