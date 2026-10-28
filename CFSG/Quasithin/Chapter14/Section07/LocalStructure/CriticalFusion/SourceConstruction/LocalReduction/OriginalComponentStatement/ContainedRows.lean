module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearTwo
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement

/-!
# The contained binary L₂ row contributes the source carrier

For an actual component whose quotient is `PSL₂(E)`, the preceding 14.7.41
contained-row argument forces `Nat.card E = 4`.  The literal quotient is then
transported through the proved `PSL₂(4) ≃ A₅` equivalence, giving exactly the
alternating row in `WholeResidualAssembly.ComponentRows`.

This is only the carrier conclusion used by 14.7.47; it does not identify a
selected component with the whole residual or discharge the other component
rows.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open WholeResidualAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A contained binary L₂ component is the literal A₅ carrier row. -/
theorem local_linearTwo_contained_component_row
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    ComponentRows (C ⧸ pCore 2 C) := by
  have hn2 := local_linearTwo_contained_field_four d h hab structural previous
    faithful earlier I hI C hC hin hE hn e
  have hcard : Nat.card E = 4 := by
    rw [hE, hn2]
    norm_num
  exact Or.inr (Or.inl ⟨5, by decide, by decide,
    ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      hcard).some⟩⟩)

/-!
The binary `L₃(2)` endpoint is already one of the literal linear carriers in
the source list.  This transport is kept separate from the field-four
restriction above: it uses the actual quotient equivalence supplied for the
component and does not infer a model from a selected row.
-/

/-- A contained binary projective `L₃(2)` component is the literal `SL₃(2)` row. -/
theorem local_linearThree_binary_contained_component_row
    (C : Type*) [Group C]
    (e : C ≃* Matrix.PSL3Two.PSL) :
    ComponentRows C := by
  exact Or.inl ⟨3, by decide, by decide,
    ⟨e.trans Matrix.PSL3Two.equiv.symm⟩⟩

/-- The same binary endpoint applied to an actual original component. -/
theorem local_linearThree_binary_contained_component_row_at
    (_d : Counterexample T L)
    (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (_hab : IsMulCommutative F.U)
    (_structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (_previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (_faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (_earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (_hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (_hC : C.IsCComponent)
    (_hin : F.Li L 1 ≤ C.map I.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) :
    ComponentRows (C ⧸ pCore 2 C) := by
  exact local_linearThree_binary_contained_component_row (C ⧸ pCore 2 C) e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
