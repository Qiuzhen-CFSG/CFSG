module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves

/-!
# Supported words lie in the Ree counting sections

Every supported positive word is a product of the literal root generators of
the named subgroup. Central B₂ factors belong to the main root subgroup by
the proved B₂ product law. This is the easy direction of the coordinate
characterization; the reverse direction requires collecting products.

Source: GLS3 Lemma 3.3.9 and the root conventions in 2.4.5–6,
`refs/KGroup/GLS3/chapter3.tex` and `chapter2.tex`.
-/
public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations
open Subgroup Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates

private theorem wordElement_mem (m : ℕ) (p : PositiveParameters m) (H : Subgroup (Model m))
    (hp : ∀ j : Fin 4, mainElement m (positiveRootWordLayout.pairIndex j) (p.pair j) ∈ H)
    (hm : ∀ j : Fin 4, mainElement m (positiveRootWordLayout.quartetIndex j) (p.main j) ∈ H)
    (hc : ∀ j : Fin 4, centralElement m (positiveRootWordLayout.quartetIndex j) (p.central j) ∈ H) :
    wordElement m p ∈ H := by
  apply H.mul_mem
  · apply H.list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hp j
  · apply H.list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact H.mul_mem (hm j) (hc j)

/-- Every positive word with the specified support lies in D. -/
theorem wordElement_mem_D (m : ℕ) (p : PositiveParameters m)
    (h : DSupport p) : wordElement m p ∈ D m := by
  rcases h with ⟨hp0, hm0, hm2⟩
  have hY0 : Y m 0 ≤ D m := ((le_sup_left).trans le_sup_left).trans le_sup_left
  have hX1 : X m 1 ≤ D m := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have hX2 : X m 2 ≤ D m := (((le_sup_left).trans le_sup_left).trans le_sup_right).trans le_sup_left
  have hX3 : X m 3 ≤ D m := (((le_sup_right).trans le_sup_left).trans le_sup_right).trans le_sup_left
  have hX4 : X m 4 ≤ D m := ((le_sup_right).trans le_sup_right).trans le_sup_left
  have hX5 : X m 5 ≤ D m := (le_sup_left).trans le_sup_right
  have hY6 : Y m 6 ≤ D m := (le_sup_right).trans le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ D m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ D m
      exact hX1 (mainElement_mem_X m 1 _)
    · change mainElement m 5 (p.pair 2) ∈ D m
      exact hX5 (mainElement_mem_X m 5 _)
    · change mainElement m 3 (p.pair 3) ∈ D m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ D m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ D m
      exact hX4 (mainElement_mem_X m 4 _)
    · change mainElement m 6 (p.main 2) ∈ D m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ D m
      exact hX2 (mainElement_mem_X m 2 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ D m
      exact hY0 (centralElement_mem_Y m 0 _)
    · change centralElement m 4 (p.central 1) ∈ D m
      exact hX4 (Y_le_X m 4 (by decide) (centralElement_mem_Y m 4 _))
    · change centralElement m 6 (p.central 2) ∈ D m
      exact hY6 (centralElement_mem_Y m 6 _)
    · change centralElement m 2 (p.central 3) ∈ D m
      exact hX2 (Y_le_X m 2 (by decide) (centralElement_mem_Y m 2 _))

/-- Every positive word with the specified support lies in D₁. -/
theorem wordElement_mem_D₁ (m : ℕ) (p : PositiveParameters m)
    (h : D₁Support p) : wordElement m p ∈ D₁ m := by
  rcases h with ⟨⟨hp0, hm0, hm2⟩, hp2, hc2⟩
  have hY0 : Y m 0 ≤ D₁ m := (le_sup_left).trans le_sup_left
  have hX1 : X m 1 ≤ D₁ m := (le_sup_right).trans le_sup_left
  have hX2 : X m 2 ≤ D₁ m := ((le_sup_left).trans le_sup_left).trans le_sup_right
  have hX3 : X m 3 ≤ D₁ m := ((le_sup_right).trans le_sup_left).trans le_sup_right
  have hX4 : X m 4 ≤ D₁ m := (le_sup_right).trans le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ D₁ m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ D₁ m
      exact hX1 (mainElement_mem_X m 1 _)
    · change mainElement m 5 (p.pair 2) ∈ D₁ m
      simp only [hp2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 3 (p.pair 3) ∈ D₁ m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ D₁ m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ D₁ m
      exact hX4 (mainElement_mem_X m 4 _)
    · change mainElement m 6 (p.main 2) ∈ D₁ m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ D₁ m
      exact hX2 (mainElement_mem_X m 2 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ D₁ m
      exact hY0 (centralElement_mem_Y m 0 _)
    · change centralElement m 4 (p.central 1) ∈ D₁ m
      exact hX4 (Y_le_X m 4 (by decide) (centralElement_mem_Y m 4 _))
    · change centralElement m 6 (p.central 2) ∈ D₁ m
      simp only [hc2, centralElement_zero, Subgroup.one_mem]
    · change centralElement m 2 (p.central 3) ∈ D₁ m
      exact hX2 (Y_le_X m 2 (by decide) (centralElement_mem_Y m 2 _))

/-- Every positive word with the specified support lies in D₂. -/
theorem wordElement_mem_D₂ (m : ℕ) (p : PositiveParameters m)
    (h : D₂Support p) : wordElement m p ∈ D₂ m := by
  rcases h with ⟨⟨hp0, hm0, hm2⟩, hp1, hc0⟩
  have hX2 : X m 2 ≤ D₂ m := ((le_sup_left).trans le_sup_left).trans le_sup_left
  have hX3 : X m 3 ≤ D₂ m := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have hX4 : X m 4 ≤ D₂ m := (le_sup_right).trans le_sup_left
  have hX5 : X m 5 ≤ D₂ m := (le_sup_left).trans le_sup_right
  have hY6 : Y m 6 ≤ D₂ m := (le_sup_right).trans le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ D₂ m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ D₂ m
      simp only [hp1, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 5 (p.pair 2) ∈ D₂ m
      exact hX5 (mainElement_mem_X m 5 _)
    · change mainElement m 3 (p.pair 3) ∈ D₂ m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ D₂ m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ D₂ m
      exact hX4 (mainElement_mem_X m 4 _)
    · change mainElement m 6 (p.main 2) ∈ D₂ m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ D₂ m
      exact hX2 (mainElement_mem_X m 2 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ D₂ m
      simp only [hc0, centralElement_zero, Subgroup.one_mem]
    · change centralElement m 4 (p.central 1) ∈ D₂ m
      exact hX4 (Y_le_X m 4 (by decide) (centralElement_mem_Y m 4 _))
    · change centralElement m 6 (p.central 2) ∈ D₂ m
      exact hY6 (centralElement_mem_Y m 6 _)
    · change centralElement m 2 (p.central 3) ∈ D₂ m
      exact hX2 (Y_le_X m 2 (by decide) (centralElement_mem_Y m 2 _))

/-- Every positive word with the specified support lies in T₁. -/
theorem wordElement_mem_T₁ (m : ℕ) (p : PositiveParameters m)
    (h : T₁Support p) : wordElement m p ∈ T₁ m := by
  rcases h with ⟨⟨⟨hp0, hm0, hm2⟩, hp2, hc2⟩, hm1, hm3⟩
  have hY0 : Y m 0 ≤ T₁ m := (le_sup_left).trans le_sup_left
  have hX1 : X m 1 ≤ T₁ m := (le_sup_right).trans le_sup_left
  have hY2 : Y m 2 ≤ T₁ m := ((le_sup_left).trans le_sup_left).trans le_sup_right
  have hX3 : X m 3 ≤ T₁ m := ((le_sup_right).trans le_sup_left).trans le_sup_right
  have hY4 : Y m 4 ≤ T₁ m := (le_sup_right).trans le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ T₁ m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ T₁ m
      exact hX1 (mainElement_mem_X m 1 _)
    · change mainElement m 5 (p.pair 2) ∈ T₁ m
      simp only [hp2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 3 (p.pair 3) ∈ T₁ m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ T₁ m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ T₁ m
      simp only [hm1, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 6 (p.main 2) ∈ T₁ m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ T₁ m
      simp only [hm3, mainElement_zero, Subgroup.one_mem]
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ T₁ m
      exact hY0 (centralElement_mem_Y m 0 _)
    · change centralElement m 4 (p.central 1) ∈ T₁ m
      exact hY4 (centralElement_mem_Y m 4 _)
    · change centralElement m 6 (p.central 2) ∈ T₁ m
      simp only [hc2, centralElement_zero, Subgroup.one_mem]
    · change centralElement m 2 (p.central 3) ∈ T₁ m
      exact hY2 (centralElement_mem_Y m 2 _)

/-- Every positive word with the specified support lies in T₂. -/
theorem wordElement_mem_T₂ (m : ℕ) (p : PositiveParameters m)
    (h : T₂Support p) : wordElement m p ∈ T₂ m := by
  rcases h with ⟨⟨⟨hp0, hm0, hm2⟩, hp1, hc0⟩, hm1, hm3⟩
  have hY2 : Y m 2 ≤ T₂ m := ((le_sup_left).trans le_sup_left).trans le_sup_left
  have hX3 : X m 3 ≤ T₂ m := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have hY4 : Y m 4 ≤ T₂ m := (le_sup_right).trans le_sup_left
  have hX5 : X m 5 ≤ T₂ m := (le_sup_left).trans le_sup_right
  have hY6 : Y m 6 ≤ T₂ m := (le_sup_right).trans le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ T₂ m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ T₂ m
      simp only [hp1, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 5 (p.pair 2) ∈ T₂ m
      exact hX5 (mainElement_mem_X m 5 _)
    · change mainElement m 3 (p.pair 3) ∈ T₂ m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ T₂ m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ T₂ m
      simp only [hm1, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 6 (p.main 2) ∈ T₂ m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ T₂ m
      simp only [hm3, mainElement_zero, Subgroup.one_mem]
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ T₂ m
      simp only [hc0, centralElement_zero, Subgroup.one_mem]
    · change centralElement m 4 (p.central 1) ∈ T₂ m
      exact hY4 (centralElement_mem_Y m 4 _)
    · change centralElement m 6 (p.central 2) ∈ T₂ m
      exact hY6 (centralElement_mem_Y m 6 _)
    · change centralElement m 2 (p.central 3) ∈ T₂ m
      exact hY2 (centralElement_mem_Y m 2 _)

/-- Every positive word with the specified support lies in K. -/
theorem wordElement_mem_K (m : ℕ) (p : PositiveParameters m)
    (h : KSupport p) : wordElement m p ∈ K m := by
  rcases h with ⟨⟨hp0, hm0, hm2⟩, hc2⟩
  have hY0 : Y m 0 ≤ K m := ((le_sup_left).trans le_sup_left).trans le_sup_left
  have hX1 : X m 1 ≤ K m := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have hX2 : X m 2 ≤ K m := (((le_sup_left).trans le_sup_left).trans le_sup_right).trans le_sup_left
  have hX3 : X m 3 ≤ K m := (((le_sup_right).trans le_sup_left).trans le_sup_right).trans le_sup_left
  have hX4 : X m 4 ≤ K m := ((le_sup_right).trans le_sup_right).trans le_sup_left
  have hX5 : X m 5 ≤ K m := le_sup_right
  apply wordElement_mem
  · simp only [positive_pair_indices]
    intro j
    fin_cases j
    · change mainElement m 7 (p.pair 0) ∈ K m
      simp only [hp0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 1 (p.pair 1) ∈ K m
      exact hX1 (mainElement_mem_X m 1 _)
    · change mainElement m 5 (p.pair 2) ∈ K m
      exact hX5 (mainElement_mem_X m 5 _)
    · change mainElement m 3 (p.pair 3) ∈ K m
      exact hX3 (mainElement_mem_X m 3 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change mainElement m 0 (p.main 0) ∈ K m
      simp only [hm0, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 4 (p.main 1) ∈ K m
      exact hX4 (mainElement_mem_X m 4 _)
    · change mainElement m 6 (p.main 2) ∈ K m
      simp only [hm2, mainElement_zero, Subgroup.one_mem]
    · change mainElement m 2 (p.main 3) ∈ K m
      exact hX2 (mainElement_mem_X m 2 _)
  · simp only [positive_quartet_indices]
    intro j
    fin_cases j
    · change centralElement m 0 (p.central 0) ∈ K m
      exact hY0 (centralElement_mem_Y m 0 _)
    · change centralElement m 4 (p.central 1) ∈ K m
      exact hX4 (Y_le_X m 4 (by decide) (centralElement_mem_Y m 4 _))
    · change centralElement m 6 (p.central 2) ∈ K m
      simp only [hc2, centralElement_zero, Subgroup.one_mem]
    · change centralElement m 2 (p.central 3) ∈ K m
      exact hX2 (Y_le_X m 2 (by decide) (centralElement_mem_Y m 2 _))

end ReeF4.ElementaryTwoBound.RootCalculations
