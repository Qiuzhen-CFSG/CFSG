module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Preparation
public import Theory.GroupTheory.MinimalParabolicGeneration.Refinement
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable

/-!
# Actual minimal parabolics from a solvable cover of the source join

Refine a specified solvable cover of Y by McBride's lemma inside each cover
member. Every retained subgroup is an actual minimal parabolic over the
original Sylow, and is solvable by its literal inclusion in a cover member.
The source central involution then gives its exact generation parameter one.

This is an adapter for model constructions, including solvable flag covers;
it does not assert that such a cover exists in every remaining model.
Source: Aschbacher--Smith B.6.3--4, E.1.13 and 10.3.3, pp.112--113,214,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- A specified solvable cover gives the family required by the model
obligation. No assertion about other minimal parabolics is needed. -/
theorem eGenerated_family_of_solvable_cover {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (Γ : Set (Subgroup Y))
    (hΓ : ∀ H ∈ Γ, ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) ≤ H ∧
      Group.IsSolvable H)
    (hgen : sSup Γ ⊔ normalizer (T.subtype hTY : Set Y) = ⊤) :
    ∃ Δ : Set (Subgroup Y),
      (∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver (T.subtype hTY) P ∧ IsEGenerated 1 P) ∧
      sSup Δ ⊔ normalizer (T.subtype hTY : Set Y) = ⊤ := by
  let S := T.subtype hTY
  let Δ := {P : Subgroup Y | ChapterB.IsMinimalParabolicOver S P ∧ ∃ H ∈ Γ, P ≤ H}
  refine ⟨Δ, ?_, ?_⟩
  · rintro P ⟨hP, H, hH, hPH⟩
    let : Group.IsSolvable H := (hΓ H hH).2
    let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hPH) (inclusion_injective hPH)
    exact ⟨hP, isEGenerated_one_of_solvable⟩
  · exact (refined_nonNormalUniqueMaximal_sup_normalizer
      (S : Subgroup Y) Γ (fun H hH => (hΓ H hH).1)).trans hgen

/-- Application to the literal component-orbit join in the task contract.
The same refined family has n(P)=1 and the required intrinsic normalizer. -/
theorem parameter_one_family_of_solvable_cover (d : CentralizerData T D s)
    (I : Subgroup G)
    (Γ : Set (Subgroup (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)))
    (hΓ : ∀ H ∈ Γ,
      ((T.subtype le_sup_right : Sylow 2
        (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) : Subgroup _) ≤ H ∧
      Group.IsSolvable H)
    (hgen : sSup Γ ⊔ normalizer ((T.subtype le_sup_right : Sylow 2
      (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) : Set _) = ⊤) :
    let Y := componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G)
    let S : Sylow 2 Y := T.subtype le_sup_right
    ∃ Δ : Set (Subgroup Y),
      (∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver S P ∧ generationParameter P = 1) ∧
      sSup Δ ⊔ normalizer (S : Set Y) = ⊤ := by
  obtain ⟨Δ, hΔ, hgen⟩ := eGenerated_family_of_solvable_cover le_sup_right Γ hΓ hgen
  exact ⟨Δ, family_parameters_one d le_sup_right Δ hΔ, hgen⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
