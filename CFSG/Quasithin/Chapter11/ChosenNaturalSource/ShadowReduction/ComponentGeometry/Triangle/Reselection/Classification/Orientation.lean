module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Projection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Choice
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Rows

/-!
# The orders of the actual field-four triangle quotients

The two orientation clauses carry genuine model isomorphisms. Their group
orders distinguish the two rows in both the orbit and chosen-seed arguments.
Source: Aschbacher--Smith 11.1.2(3), printed pp.762--764.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

omit [Finite G] in
/-- The two source model clauses give their actual quotient orders. -/
theorem orientation_order (ho : TriangleOrientation L I) :
    FieldFourOrder (Nat.card (I ⧸ pCore 2 I)) := by
  rcases ho with ⟨_, F, hF, hfin, hc, ⟨e⟩⟩ | ⟨_, F, hF, hfin, hc, ⟨e⟩⟩
  · let := hF
    let := hfin
    apply Or.inl
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, hc]
    norm_num
  · let := hF
    let := hfin
    apply Or.inr
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hc]
    norm_num

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
