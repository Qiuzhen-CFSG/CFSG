module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.IndexBound
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Counting
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.EndpointSquares

/-!
# The first half of the Ree elementary-subgroup argument

The replacement is the actual subgroup (E ∩ C) ⊔ V of the fixed matrix model.
The finite-group counting argument proves that it is elementary and at least
as large as E. The square calculation in C then places every element in D.
The centralizer geometry supplies the counting hypotheses. The literal positive
coordinates of an element of C have zero X₈ parameter, so the endpoint Suzuki
square laws force its X₁ and X₇ main parameters to vanish. This places each
element of the elementary replacement in D, without assuming a quotient
decomposition or the independent `RootCalculationFacts`.

`replacement_in_D` proves the source's explicit construction, and
`exists_elementary_le_D` supplies exactly the unconditional `hreplace` argument
of `ElementaryTwoBound.card_le_of_root_calculations`. The earlier conditional
interfaces are retained.

Source: GLS3 Lemma 3.3.9, first paragraph of the proof, printed p.135,
`refs/KGroup/GLS3/chapter3.tex`. The field order Q = 2^(2m+1) is GLS's q².
-/

public section
namespace ReeF4.ElementaryTwoBound.Replacement
open Subgroup Parabolics

/-- The first replacement, with the literal centralizer and cardinal inputs
still explicit. It gives the actual subgroup used in the source. -/
theorem replacement_in_C_of_calculations (m : ℕ) (h : CentralizerCalculations m)
    (E : Subgroup (Model m)) (hEU : E ≤ unipotent m) (hE : IsElementaryAbelian 2 E) :
    (E ⊓ C m) ⊔ V m ≤ C m ∧
      IsElementaryAbelian 2 ((E ⊓ C m) ⊔ V m : Subgroup (Model m)) ∧
      Nat.card E ≤ Nat.card ((E ⊓ C m) ⊔ V m : Subgroup (Model m)) :=
  elementary_central_replacement 2 (2 ^ (2 * m + 1))
    (unipotent m) (C m) (V m) (Z m) E (C_le_unipotent m) (V_le_C m)
    h.centralizes h.elementary_V h.outside (card_unipotent_le_field_mul_C m) h.card_V hEU hE

/-- The precise `hreplace` interface, conditional on the two independent root
calculations. The endpoint calculation is square support in C, not a rank bound. -/
theorem exists_elementary_le_D_of_calculations (m : ℕ) (h : CentralizerCalculations m)
    (hsquare : ∀ x ∈ C m, x ^ 2 = 1 → x ∈ D m)
    (E : Subgroup (Model m)) (hEU : E ≤ unipotent m) (hE : IsElementaryAbelian 2 E) :
    ∃ F : Subgroup (Model m), F ≤ D m ∧ IsElementaryAbelian 2 F ∧
      Nat.card E ≤ Nat.card F := by
  obtain ⟨hFC, hF, hcard⟩ := replacement_in_C_of_calculations m h E hEU hE
  let := hF
  refine ⟨(E ⊓ C m) ⊔ V m, ?_, hF, hcard⟩
  intro x hx
  exact hsquare x (hFC hx) (elemPow_eq_one_of_isElementaryAbelian x hx)

/-- Every square-one element of C lies in D. The centralizer calculation
removes X₈ from its actual positive word; the endpoint square laws then remove
the two noncentral endpoint parameters. -/
theorem mem_D_of_mem_C_sq (m : ℕ) (x : Model m) (hx : x ∈ C m)
    (hsquare : x ^ 2 = 1) : x ∈ D m := by
  obtain ⟨p, hp⟩ := NormalizedRootCentralizers.CenterExponent.exists_positiveWord
    m x (C_le_unipotent m hx)
  exact mem_D_of_positiveWord_sq m p (pair_eighth_eq_zero_of_mem_C m x hx p hp)
    x hp hsquare

/-- The explicit replacement from the first paragraph of GLS3 Lemma 3.3.9
is elementary, lies in D, and has at least the original subgroup's order. -/
theorem replacement_in_D (m : ℕ) (hm : 1 ≤ m)
    (E : Subgroup (Model m)) (hEU : E ≤ unipotent m) (hE : IsElementaryAbelian 2 E) :
    (E ⊓ C m) ⊔ V m ≤ D m ∧
      IsElementaryAbelian 2 ((E ⊓ C m) ⊔ V m : Subgroup (Model m)) ∧
      Nat.card E ≤ Nat.card ((E ⊓ C m) ⊔ V m : Subgroup (Model m)) := by
  obtain ⟨hFC, hF, hcard⟩ :=
    replacement_in_C_of_calculations m (centralizerCalculations m hm) E hEU hE
  let := hF
  refine ⟨?_, hF, hcard⟩
  intro x hx
  exact mem_D_of_mem_C_sq m x (hFC hx) (elemPow_eq_one_of_isElementaryAbelian x hx)

/-- The unconditional `hreplace` input to
`ElementaryTwoBound.card_le_of_root_calculations`. The witness is (E ∩ C)V
in the literal fixed matrix group; no rank or root-calculation premise remains. -/
theorem exists_elementary_le_D (m : ℕ) (hm : 1 ≤ m)
    (E : Subgroup (Model m)) (hEU : E ≤ unipotent m) (hE : IsElementaryAbelian 2 E) :
    ∃ F : Subgroup (Model m), F ≤ D m ∧ IsElementaryAbelian 2 F ∧
      Nat.card E ≤ Nat.card F :=
  ⟨(E ⊓ C m) ⊔ V m, replacement_in_D m hm E hEU hE⟩

end ReeF4.ElementaryTwoBound.Replacement
