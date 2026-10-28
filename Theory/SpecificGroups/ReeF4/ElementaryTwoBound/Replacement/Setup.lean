module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootSubgroups

/-!
# Root sections for the Ree elementary-subgroup replacement

The source uses C = X₁⋯X₇, C₀ = X₂⋯X₆, V = Y₃Y₅ and Z = Y₅.
Here these are literal subgroup joins in the fixed matrix carrier; no product,
normality or centralizer assertion is built into their definitions. The B₂
product with first parameter 1 puts each central curve in its main root group.
In particular V lies in C and all the sections lie in the actual unipotent group.

Source: GLS3 Lemma 3.3.9, first paragraph of the proof, printed p.135,
`refs/KGroup/GLS3/chapter3.tex`, and Table 2.4 / 2.4.5(d).
-/

@[expose] public section
noncomputable section

namespace ReeF4.ElementaryTwoBound.Replacement
open Subgroup Parabolics
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The source section X₂⋯X₆; normality in C is a separate root calculation. -/
def C₀ (m : ℕ) : Subgroup (Model m) :=
  X m 1 ⊔ X m 2 ⊔ X m 3 ⊔ X m 4 ⊔ X m 5

/-- The source section X₁⋯X₇. -/
def C (m : ℕ) : Subgroup (Model m) := X m 0 ⊔ C₀ m ⊔ X m 6

/-- The central root group Y₅ in the replacement argument. -/
def Z (m : ℕ) : Subgroup (Model m) := Y m 4

/-- The source elementary section Y₃Y₅, defined without assuming its geometry. -/
def V (m : ℕ) : Subgroup (Model m) := Y m 2 ⊔ Z m

/-- Main parameters generate the central curve in each Suzuki root group. -/
theorem Y_le_X (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0) : Y m i ≤ X m i := by
  apply (closure_le _).mpr
  rintro _ ⟨t, rfl⟩
  have hmain (a : CoefficientField m) : mainElement m i a ∈ X m i :=
    subset_closure ⟨a, rfl⟩
  have heq : centralElement m i t =
      (mainElement m i (1 + t))⁻¹ * (mainElement m i 1 * mainElement m i t) := by
    apply Subtype.ext
    change centralWord m i t =
      (rootWord m i (1 + t))⁻¹ * (rootWord m i 1 * rootWord m i t)
    rw [mainParameterProduct m i hi t, inv_mul_cancel_left]
  rw [heq]
  exact (X m i).mul_mem ((X m i).inv_mem (hmain _))
    ((X m i).mul_mem (hmain _) (hmain _))

theorem C₀_le_C (m : ℕ) : C₀ m ≤ C m :=
  le_sup_of_le_left le_sup_right

theorem C_le_unipotent (m : ℕ) : C m ≤ unipotent m := by
  exact sup_le (sup_le (X_le_unipotent m 0)
    (sup_le (sup_le (sup_le (sup_le (X_le_unipotent m 1) (X_le_unipotent m 2))
      (X_le_unipotent m 3)) (X_le_unipotent m 4)) (X_le_unipotent m 5)))
    (X_le_unipotent m 6)

theorem V_le_C (m : ℕ) : V m ≤ C m := by
  apply sup_le
  · exact (Y_le_X m 2 (by decide)).trans
      ((le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))).trans
        (C₀_le_C m))
  · exact (Y_le_X m 4 (by decide)).trans
      ((le_sup_of_le_left le_sup_right).trans (C₀_le_C m))

theorem Z_le_V (m : ℕ) : Z m ≤ V m := le_sup_right

theorem D_le_C (m : ℕ) : D m ≤ C m := by
  have h₀ : Y m 0 ≤ C m :=
    (Y_le_X m 0 (by decide)).trans (le_sup_of_le_left le_sup_left)
  have h₆ : Y m 6 ≤ C m := (Y_le_X m 6 (by decide)).trans le_sup_right
  have h₁ : X m 1 ≤ C₀ m :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have h₂ : X m 2 ≤ C₀ m :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have h₃ : X m 3 ≤ C₀ m := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have h₄ : X m 4 ≤ C₀ m := le_sup_of_le_left le_sup_right
  have h₅ : X m 5 ≤ C₀ m := le_sup_right
  exact sup_le (sup_le (sup_le h₀ (h₁.trans (C₀_le_C m)))
    (sup_le (sup_le (h₂.trans (C₀_le_C m)) (h₃.trans (C₀_le_C m)))
      (h₄.trans (C₀_le_C m)))) (sup_le (h₅.trans (C₀_le_C m)) h₆)

/-- The centralizer and cardinal calculations for the first replacement step.
These concern fixed root sections and contain no assertion about an arbitrary
elementary subgroup or its replacement. -/
structure CentralizerCalculations (m : ℕ) : Prop where
  elementary_V : IsElementaryAbelian 2 (V m)
  centralizes : C m ≤ centralizer (V m : Set (Model m))
  outside : ∀ x ∈ unipotent m, x ∉ C m →
    V m ⊓ centralizer ({x} : Set (Model m)) ≤ Z m
  card_V : (2 ^ (2 * m + 1)) * Nat.card (Z m) ≤ Nat.card (V m)

end ReeF4.ElementaryTwoBound.Replacement
