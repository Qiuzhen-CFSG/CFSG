module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.Source
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.Source

/-!
# Plane uniqueness directly from the original residual input

Failure of uniqueness selects a minimal escaping H-overgroup. The direct
characteristic-two source theorem forces an ordinary component, while the
source ordinary branch excludes it. This gives the literal distinguished-plane
uniqueness needed by the original critical-pair contradiction without a
partner residual identity or a PlaneUniquenessPreceding packet.

Source: Aschbacher--Smith 15.2.15--24 and 15.2.27--28,
printed pp.1112--1120, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The actual residual input and original global wreath quotients give the
singleton maximal-overgroup family of the distinguished-plane centralizer. -/
theorem ChosenGeometry.ResidualInput.plane_uniqueness_direct
    (r : ResidualInput h H B)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath)) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V,B⁆ : Subgroup G)) = {Mc} := by
  by_contra hne
  obtain ⟨I,hI⟩ := r.exists_minimal_escape_direct hne
  obtain ⟨he,_,_,_⟩ := source_chosen_index_two_equality_row h r hquotient
  exact r.ordinary_minimal_escape_false hquotient hI
    (r.escaping_not_characteristicTwo_of_eq he hI.1)

/-- The original chosen-action contradiction from one actual residual input.
No residual identity, plane-uniqueness or model-action premise remains. -/
theorem source_chosen_contradiction_of_residual_input
    (h : ChosenSmallSource T M Mc V) (r : ResidualInput h H B)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath)) : False :=
  source_chosen_contradiction_of_residual_input_and_uniqueness h r hquotient
    (r.plane_uniqueness_direct hquotient)


/-- The original global wreath quotients supply the actual residual input;
no separate residual identity or residual structure premise is required. -/
theorem source_chosen_contradiction_of_wreath_quotients
    (h : ChosenSmallSource T M Mc V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath)) : False := by
  obtain ⟨H,hH,_,he⟩ := h.exists_wreath_local hquotient
  obtain ⟨B,r⟩ := h.exists_residualInput_of_preceding h.action_alternatives hH he htwo
  exact source_chosen_contradiction_of_residual_input h r hquotient

end CFSG.Quasithin.Chapter15.Section02
