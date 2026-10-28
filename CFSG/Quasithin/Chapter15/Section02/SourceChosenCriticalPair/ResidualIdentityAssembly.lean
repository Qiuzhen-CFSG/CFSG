module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.DistinguishedPlane
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.HeldExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualPlaneAssembly

/-!
# Chosen-action contradiction from residual identities

The common-plane construction supplies the actual inverter and centralization
for every H-star residual. Select one original residual input and use its
identity to discharge plane uniqueness. The complete residual-input consumer
supplies partner-core containment, including the equality and Held rows.

The earlier two-overgroup and wreath-quotient clauses, and the residual
identities themselves, remain explicit source inputs.

Source: Aschbacher--Smith, 15.2.12 and 15.2.27--28, printed pp.1111,1119--1120.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The original residual identities suffice for the chosen-action
contradiction: the retained Held alternative is discharged internally. -/
theorem source_chosen_contradiction_of_residual_identities
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (hresidual : ∀ H B, ResidualInput h H B →
      partnerSpan H Mc = threePrimeResidual Mc) : False := by
  obtain ⟨H,hH,_,he⟩ := h.exists_wreath_local hquotient
  obtain ⟨B,d⟩ := h.exists_residualInput_of_preceding h.action_alternatives hH he htwo
  exact source_chosen_contradiction_of_one_residual_identity h d hquotient
    (hresidual H B d)

end CFSG.Quasithin.Chapter15.Section02
