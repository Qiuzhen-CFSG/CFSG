module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.CubicModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.Basic

/-!
# Applying the concrete cubic witnesses to the local components

The actual actor or factor presentation now discharges every cubic premise of
`all_components_commutator_of_quasisimple_model` and its product analogue.
The star quotient, component convention and local theta identity are exactly
those of `Basic`. Quasisimplicity is inherited from the component branch, and
solvability of Y₀ is supplied there by `Y0_solvable_of_extraspecial`.

These are the commutator clauses in the perfect alternatives of 15.3.49(i),
printed pp.1143–1144, using the concrete group list in B.5.6, printed p.105.
They do not assert the separate absorption of the two-core kernel.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
variable {G : Type*} [Group G] [Finite G]

/-- The concrete single-actor catalogue discharges the cubic hypothesis of the
existing local component-commutator argument. -/
theorem all_components_commutator_of_perfectActorModel {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D] (hD : PerfectActorModel D)
    (H M Y0 A : Subgroup G) [Group.IsSolvable Y0]
    (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (e : starImage H (localSpan A H) ≃* D) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent → L = ⁅L, Y0⁆ := by
  obtain ⟨x, hx, hn⟩ := hD.exists_noncentral_cubic
  exact all_components_commutator_of_quasisimple_model H M Y0 A
    hAH hYH hY hN hQM hθ e x hx hn

/-- Both factors' cubic hypotheses are discharged with their literal model
isomorphisms, including the projective degree-three factors. -/
theorem all_components_commutator_of_perfectFactorModels {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E]
    (hD : PerfectFactorModel D) (hE : PerfectFactorModel E)
    (H M Y0 A : Subgroup G) [Group.IsSolvable Y0]
    (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (e : starImage H (localSpan A H) ≃* D × E) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent → L = ⁅L, Y0⁆ := by
  obtain ⟨x, hx, hn⟩ := hD.exists_noncentral_cubic
  obtain ⟨z, hz, hzn⟩ := hE.exists_noncentral_cubic
  exact all_components_commutator_of_product_model H M Y0 A
    hAH hYH hY hN hQM hθ e x hx hn z hz hzn

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
