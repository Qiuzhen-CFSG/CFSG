module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
public import Theory.ElementaryAbelian.Basic

/-!
# The root subgroups in the Ree elementary-rank argument

These are subgroups of the literal fixed matrix carrier. `X m i` is generated
by the main relative-root curve, and `Y m i` by the central curve (the latter
is used only for even indices). Indices are zero based: `X m 1` is source X₂.
The named joins are precisely the subgroups used in GLS3 Lemma 3.3.9.

`RootCalculationFacts` specifies the remaining square, commutator and order
calculations. It does not assert an elementary-subgroup bound. The counting
argument consumes these facts separately from the initial replacement into D.
In particular both sides of the source's symmetric square argument are explicit.

Source: GLS3, Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter3.tex`, using 2.4.5(d) and 2.4.6 in `chapter2.tex`.
GLS writes q² for our coefficient-field order `2^(2*m+1)`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.ElementaryTwoBound
open Subgroup Parabolics LargeLocalSeeds
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The central curve, in the actual fixed group. Only even indices are used. -/
def centralElement (m : ℕ) (i : Fin 8) (t : CoefficientField m) : Model m :=
  ⟨centralWord m i t, by
    simpa only [mem_fixedSubgroup, reeAutomorphism_apply]
      using (positive_words_fixed_mem m i t).2.1⟩

@[simp] theorem centralElement_coe (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    toSplitGroup m (centralElement m i t) = centralWord m i t := toSplitGroup_apply m _

/-- The source relative root group Xᵢ₊₁. -/
def X (m : ℕ) (i : Fin 8) : Subgroup (Model m) :=
  closure (Set.range (mainElement m i))

/-- The central root curve Yᵢ₊₁, used at even indices. -/
def Y (m : ℕ) (i : Fin 8) : Subgroup (Model m) :=
  closure (Set.range (centralElement m i))

theorem X_le_unipotent (m : ℕ) (i : Fin 8) : X m i ≤ unipotent m := by
  apply (closure_le _).mpr
  rintro _ ⟨t, rfl⟩
  exact mainElement_mem_unipotent m i t

theorem Y_le_unipotent (m : ℕ) (i : Fin 8) : Y m i ≤ unipotent m := by
  apply (closure_le _).mpr
  rintro _ ⟨t, rfl⟩
  change toSplitGroup m (centralElement m i t) ∈ splitUnipotent m
  rw [centralElement_coe]
  exact (positive_words_fixed_mem m i t).2.2

/-- Y₁X₂. -/
def left (m : ℕ) : Subgroup (Model m) := Y m 0 ⊔ X m 1
/-- X₆Y₇. -/
def right (m : ℕ) : Subgroup (Model m) := X m 5 ⊔ Y m 6
/-- X₃X₄X₅. -/
def middle (m : ℕ) : Subgroup (Model m) := X m 2 ⊔ X m 3 ⊔ X m 4
/-- Y₃X₄Y₅. -/
def middleCenter (m : ℕ) : Subgroup (Model m) := Y m 2 ⊔ X m 3 ⊔ Y m 4
/-- The source subgroup D₁. -/
def D₁ (m : ℕ) : Subgroup (Model m) := left m ⊔ middle m
/-- The symmetric subgroup used in the source's “likewise” step. -/
def D₂ (m : ℕ) : Subgroup (Model m) := middle m ⊔ right m
/-- The source subgroup D. -/
def D (m : ℕ) : Subgroup (Model m) := D₁ m ⊔ right m
/-- The square-one locus in D₁, once the root calculation is supplied. -/
def T₁ (m : ℕ) : Subgroup (Model m) := left m ⊔ middleCenter m
/-- The square-one locus in D₂, once the symmetric calculation is supplied. -/
def T₂ (m : ℕ) : Subgroup (Model m) := middleCenter m ⊔ right m
/-- Y₁X₂X₃X₄X₅X₆, containing the relevant centralizer in D. -/
def K (m : ℕ) : Subgroup (Model m) := D₁ m ⊔ X m 5

theorem D_le_unipotent (m : ℕ) : D m ≤ unipotent m := by
  exact sup_le
    (sup_le (sup_le (Y_le_unipotent m 0) (X_le_unipotent m 1))
      (sup_le (sup_le (X_le_unipotent m 2) (X_le_unipotent m 3))
        (X_le_unipotent m 4)))
    (sup_le (X_le_unipotent m 5) (Y_le_unipotent m 6))

/-- Literal root-calculation inputs for the second half of GLS3 Lemma 3.3.9.
No field assumes the conclusion about elementary subgroups. -/
structure RootCalculationFacts (m : ℕ) : Prop where
  card_D : Nat.card (D m) = (2 ^ (2 * m + 1)) ^ 9
  card_D₁ : Nat.card (D₁ m) = (2 ^ (2 * m + 1)) ^ 7
  card_D₂ : Nat.card (D₂ m) = (2 ^ (2 * m + 1)) ^ 7
  card_T₁ : Nat.card (T₁ m) = (2 ^ (2 * m + 1)) ^ 5
  card_T₂ : Nat.card (T₂ m) = (2 ^ (2 * m + 1)) ^ 5
  card_left : Nat.card (left m) = (2 ^ (2 * m + 1)) ^ 2
  card_right : Nat.card (right m) = (2 ^ (2 * m + 1)) ^ 2
  card_Y₁ : Nat.card (Y m 0) = 2 ^ (2 * m + 1)
  card_K : Nat.card (K m) = (2 ^ (2 * m + 1)) ^ 8
  square_D₁ : ∀ x ∈ D₁ m, x ^ 2 = 1 → x ∈ T₁ m
  square_D₂ : ∀ x ∈ D₂ m, x ^ 2 = 1 → x ∈ T₂ m
  disjoint_Y₁_X₂ : Y m 0 ⊓ X m 1 = ⊥
  cross_commute : ∀ e ∈ left m, e ≠ 1 → ∀ f ∈ right m, f ≠ 1 →
    Commute e f → e ∈ X m 1
  centralizer_X₂ : ∀ e ∈ X m 1, e ≠ 1 →
    D m ⊓ centralizer ({e} : Set (Model m)) ≤ K m

end ReeF4.ElementaryTwoBound
