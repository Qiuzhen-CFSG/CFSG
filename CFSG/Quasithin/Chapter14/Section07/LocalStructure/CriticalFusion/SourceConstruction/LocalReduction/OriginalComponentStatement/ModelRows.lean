module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedRows
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup

/-!
# Literal model rows for an original component

The model equivalence in these bridges is an equivalence for the literal
quotient `C ⧸ O₂(C)`.  The source reduction must still construct that
equivalence and the containment of the original `L₁`; no catalogue tag or
selected-component marking is used here.
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

/-- A literal binary linear quotient is one of the linear catalogue rows. -/
theorem local_linear_model_component_row_at
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
    {n : ℕ} (hn : 3 ≤ n) (hn' : n ≤ 5)
    (e : (C ⧸ pCore 2 C) ≃* SL(n, ZMod 2)) :
    ComponentRows (C ⧸ pCore 2 C) := by
  exact Or.inl ⟨n, hn, hn', ⟨e⟩⟩

/-- A literal alternating quotient is one of the alternating catalogue rows. -/
theorem local_alternating_model_component_row_at
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
    {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 7)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin n)) :
    ComponentRows (C ⧸ pCore 2 C) := by
  exact Or.inr (Or.inl ⟨n, hn, hn', ⟨e⟩⟩)

/-- A literal binary `G₂(2)'` quotient is the exceptional catalogue row. -/
theorem local_gTwo_binary_model_component_row_at
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
    (e : (C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ComponentRows (C ⧸ pCore 2 C) := by
  exact Or.inr (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
