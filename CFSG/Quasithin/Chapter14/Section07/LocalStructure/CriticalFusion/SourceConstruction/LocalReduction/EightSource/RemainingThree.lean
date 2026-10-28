module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.RemainingRows
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Exclusion

/-!
# Original component reduction after the linear-four exclusion

The original SL₄(2) source theorem now supplies its row without a selected
module or extension-splitting premise. Together with the completed A₆, A₇
and SL₅(2) exclusions, the local row family requires only SL₃(2).
The Data constructor also retains its independent G₂ exclusion and all
original earlier-source hypotheses.

This is a source reduction, not a proof of the remaining SL₃ or G₂ duties.
Source: Aschbacher--Smith 14.7.49--53 and 14.7.63, pp.1064--1066,1069.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Only SL₃(2) remains in the actual row-exclusion family. -/
theorem row_exclusions_of_linear_three_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (linearThree : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(3,ZMod 2))) :
    RowExclusions F L := by
  apply row_exclusions_of_linear_three_four_at
    d h hab structural previous faithful earlier source47
  intro I hI C hC n hn
  rcases hn with rfl | rfl
  · exact linearThree I hI C hC
  · exact source_14_7_51_linear_four_at d h hab structural previous faithful
      earlier source47 I hI C hC

/-- Apply the completed named rows to the original Data constructor.
The remaining SL₃ exclusion and independent G₂ duty are explicit. -/
theorem exists_data_of_linear_three_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (linearThree : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(3,ZMod 2)))
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_component_statement_at d h hab structural previous faithful earlier
    source47 (row_exclusions_of_linear_three_at d h hab structural previous faithful
      earlier source47 linearThree) h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
