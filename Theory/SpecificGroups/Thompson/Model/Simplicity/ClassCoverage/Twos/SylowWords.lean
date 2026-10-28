module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Twos.LocalModel

/-!
# Explicit words for a Thompson Sylow-two candidate

These ten words in the two fixed `ThG1-max2W1` generators were obtained by
lifting a Sylow subgroup in an exploratory degree-31 quotient action.
Their values belong to the actual matrix group. The subgroup order and fusion
are separate certificate obligations: no result of the external calculation
is used as a proof. The signed source words are in `Twos/source/sylow_words.json`.
-/

@[expose] public section
namespace Thompson.Simplicity.TwoLocal.SylowCandidate

/-- Alphabet: the two local generators and their inverses. -/
def letter : Fin 4 → Model := ![localA, localA⁻¹, localB, localB⁻¹]

/-- Evaluate words in the actual matrix carrier. -/
def eval (w : List (Fin 4)) : Model := (w.map letter).prod

/-- Explicit candidate generators; their source words use signed letters 1,2. -/
def generatorWords : Fin 10 → List (Fin 4) :=
  ![[2, 2, 1, 2, 1, 3, 1, 3, 1, 3, 0, 2, 0, 2, 0, 2, 0, 3, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 2],
    [2, 2, 1, 2, 1, 3, 1, 3, 1, 3, 0, 2, 0, 2, 0, 2, 0, 3, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 0, 2, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 2, 2, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 2],
    [3, 0, 2, 0, 2, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3],
    [2, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3, 0, 2, 0, 2, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 2, 0, 2],
    [1, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3],
    [1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3],
    [2, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3],
    [2, 1, 2, 1, 3, 1, 3, 1, 3, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 3, 1, 2],
    [2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1],
    [3, 1, 2] ]

/-- Ten genuine matrix words, not abstract generators with imposed relations. -/
def generators (i : Fin 10) : Model := eval (generatorWords i)

/-- The fixed candidate whose order 32768 remains to be certified. -/
def subgroup : Subgroup Model := Subgroup.closure (Set.range generators)

theorem generators_mem (i : Fin 10) : generators i ∈ subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- All word values lie in the fixed source-word subgroup. -/
theorem eval_mem (w : List (Fin 4)) : eval w ∈ localSubgroup := by
  have hletter (i : Fin 4) : letter i ∈ localSubgroup := by
    fin_cases i
    · exact localA_mem
    · exact localSubgroup.inv_mem localA_mem
    · exact localB_mem
    · exact localSubgroup.inv_mem localB_mem
  induction w with
  | nil => exact localSubgroup.one_mem
  | cons i w ih => exact localSubgroup.mul_mem (hletter i) ih

/-- The candidate lies in the actual two-local word subgroup. -/
theorem subgroup_le : subgroup ≤ localSubgroup := by
  rw [subgroup, Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  exact eval_mem (generatorWords i)

/-- Fusion restricted to the fixed Sylow candidate suffices. -/
def InvolutionFusion : Prop :=
  ∀ y : Model, y ∈ subgroup → orderOf y = 2 →
    ∃ g : Model, generatorA = g * y * g⁻¹

end Thompson.Simplicity.TwoLocal.SylowCandidate
