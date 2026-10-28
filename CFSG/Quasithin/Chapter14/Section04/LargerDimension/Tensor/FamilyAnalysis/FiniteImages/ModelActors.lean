module

public import Theory.SpecificGroups.TensorThreeFiveActors
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.Borel

/-!
# Model calculations applied to the actual tensor actors

The source Sylow subgroup maps to the literal star image of T. Its normalization,
two-perfectness and cubic two-core quotient are inherited by every star actor.
The finite-model calculation then identifies that image with either the cubic
core or the actual relative Borel image.

The final theorem discharges both finite calculations and applies the exhaustive
model classification to the actual star actor. It supplies the image dichotomy
used in the pair-family assembly of Aschbacher–Smith, combined manuscript of
1 March 2004, Lemma 14.4.10(1), printed p.1010 (PDF p.1027).
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.TensorThreeFiveActors
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G]

/-- Apply the separate product-splitting and five-factor calculations to a
member of the literal source family. No additional kernel or Sylow premise is needed. -/
theorem star_eq_of_model_factor_calculations
    (hs : ProductSplitting Five) (ha : ProductSplitting AltFive)
    (fs : FactorActors Five) (fa : FactorActors AltFive)
    {H T X : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive))
    (hX : X ∈ XFamily H T) :
    star H X = pCore 3 (coreQuotient H) ∨ star H X = star H (borel H T) := by
  obtain ⟨Q, hQ⟩ := exists_star_sylow P hP
  have hn : (Q : Subgroup (coreQuotient H)) ≤ normalizer (star H X : Set _) := by
    rw [hQ]
    exact (star_mem_X hX).T_normalizes
  rcases model_actors_of_factors hs ha fs fa hmodel Q (star H X) hn
    (isPPerfect_of_residual_eq (star_mem_X hX).residual_eq)
    (star_quotient_card_three hX) with h | h
  · exact Or.inl h
  · rw [hQ, ← star_component H, ← star_borel_eq_relative_normalizer P hP] at h
    exact Or.inr h

/-- Every source actor has the cubic-core or actual Borel image in either
tensor model. This discharges the finite-image classification in 14.4.10(1). -/
theorem star_eq_of_model
    {H T X : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive))
    (hX : X ∈ XFamily H T) :
    star H X = pCore 3 (coreQuotient H) ∨ star H X = star H (borel H T) := by
  obtain ⟨Q, hQ⟩ := exists_star_sylow P hP
  have hn : (Q : Subgroup (coreQuotient H)) ≤ normalizer (star H X : Set _) := by
    rw [hQ]
    exact (star_mem_X hX).T_normalizes
  rcases model_actors hmodel Q (star H X) hn
    (isPPerfect_of_residual_eq (star_mem_X hX).residual_eq)
    (star_quotient_card_three hX) with h | h
  · exact Or.inl h
  · rw [hQ, ← star_component H, ← star_borel_eq_relative_normalizer P hP] at h
    exact Or.inr h

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
end
