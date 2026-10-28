module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Setup

/-!
# The index estimate for the first Ree replacement

The positive fixed factorization starts with x₈(t). All remaining main and
central factors lie in C = X₁⋯X₇. Thus multiplication gives a surjection from
the coefficient field times C onto U and proves |U| ≤ Q|C|. This is exactly
the numerical consequence of U/C ≅ X₈ needed by the replacement argument;
it requires no assumed normality or group structure on a quotient.

Source: GLS3 Lemma 3.3.9, first paragraph of the proof, printed p.135.
-/

public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.Replacement
open Subgroup Parabolics
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates

theorem X_le_C_of_ne_last (m : ℕ) (i : Fin 8) (hi : i ≠ 7) : X m i ≤ C m := by
  fin_cases i
  · exact le_sup_of_le_left le_sup_left
  · exact (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))).trans
      (C₀_le_C m)
  · exact (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))).trans
      (C₀_le_C m)
  · exact (le_sup_of_le_left (le_sup_of_le_left le_sup_right)).trans (C₀_le_C m)
  · exact (le_sup_of_le_left le_sup_right).trans (C₀_le_C m)
  · exact le_sup_right.trans (C₀_le_C m)
  · exact le_sup_right
  · exact (hi rfl).elim

theorem mainElement_mem_C (m : ℕ) (i : Fin 8) (hi : i ≠ 7) (t : CoefficientField m) :
    mainElement m i t ∈ C m :=
  X_le_C_of_ne_last m i hi (subset_closure ⟨t, rfl⟩)

theorem centralElement_mem_C (m : ℕ) (i : Fin 8) (hi : i ≠ 7)
    (he : i.val % 2 = 0) (t : CoefficientField m) : centralElement m i t ∈ C m :=
  (Y_le_X m i he).trans (X_le_C_of_ne_last m i hi) (subset_closure ⟨t, rfl⟩)

/-- Factor a specified positive word through C, retaining its exact x₈ parameter.
This also supplies the coordinate used by the separate centralizer calculation. -/
theorem exists_C_factor_of_positiveWord (m : ℕ) (x : Model m) (p : PositiveParameters m)
    (hp : toSplitGroup m x = positiveWord m p) :
    ∃ c : C m, x = mainElement m 7 (p.pair 0) * c := by
  let c : Model m :=
    (mainElement m 1 (p.pair 1) * mainElement m 5 (p.pair 2) *
      mainElement m 3 (p.pair 3)) *
    ((mainElement m 0 (p.main 0) * centralElement m 0 (p.central 0)) *
      (mainElement m 4 (p.main 1) * centralElement m 4 (p.central 1)) *
      (mainElement m 6 (p.main 2) * centralElement m 6 (p.central 2)) *
      (mainElement m 2 (p.main 3) * centralElement m 2 (p.central 3)))
  have hc : c ∈ C m := by
    have h₀ := (C m).mul_mem (mainElement_mem_C m 0 (by decide) (p.main 0))
      (centralElement_mem_C m 0 (by decide) (by decide) (p.central 0))
    have h₄ := (C m).mul_mem (mainElement_mem_C m 4 (by decide) (p.main 1))
      (centralElement_mem_C m 4 (by decide) (by decide) (p.central 1))
    have h₆ := (C m).mul_mem (mainElement_mem_C m 6 (by decide) (p.main 2))
      (centralElement_mem_C m 6 (by decide) (by decide) (p.central 2))
    have h₂ := (C m).mul_mem (mainElement_mem_C m 2 (by decide) (p.main 3))
      (centralElement_mem_C m 2 (by decide) (by decide) (p.central 3))
    exact (C m).mul_mem
      ((C m).mul_mem
        ((C m).mul_mem (mainElement_mem_C m 1 (by decide) (p.pair 1))
          (mainElement_mem_C m 5 (by decide) (p.pair 2)))
        (mainElement_mem_C m 3 (by decide) (p.pair 3)))
      ((C m).mul_mem ((C m).mul_mem ((C m).mul_mem h₀ h₄) h₆) h₂)
  refine ⟨⟨c, hc⟩, ?_⟩
  apply toSplitGroup_injective m
  change toSplitGroup m x = toSplitGroup m (mainElement m 7 (p.pair 0) * c)
  rw [hp]
  simp only [c, map_mul, mainElement_coe, centralElement_coe]
  simp [positiveWord, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, mul_assoc]

/-- The actual first root parameter and an actual element of C factor every
element of U. No uniqueness or quotient is needed for this estimate. -/
theorem exists_last_root_mul_C (m : ℕ) (x : Model m) (hx : x ∈ unipotent m) :
    ∃ (t : CoefficientField m) (c : C m), x = mainElement m 7 t * c := by
  obtain ⟨p, hp⟩ := exists_positiveWord m x hx
  obtain ⟨c, hc⟩ := exists_C_factor_of_positiveWord m x p hp
  exact ⟨p.pair 0, c, hc⟩

/-- The source's quotient-size comparison, proved on the original carrier
using the explicit multiplication map from the field times C. -/
theorem card_unipotent_le_field_mul_C (m : ℕ) :
    Nat.card (unipotent m) ≤ (2 ^ (2 * m + 1)) * Nat.card (C m) := by
  let f : CoefficientField m × C m → unipotent m := fun z =>
    ⟨mainElement m 7 z.1 * z.2,
      (unipotent m).mul_mem (mainElement_mem_unipotent m 7 z.1)
        (C_le_unipotent m z.2.property)⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨t, c, h⟩ := exists_last_root_mul_C m x x.property
    exact ⟨(t, c), Subtype.ext h.symm⟩
  simpa only [Nat.card_prod, field_card] using Nat.card_le_card_of_surjective f hf

end ReeF4.ElementaryTwoBound.Replacement
