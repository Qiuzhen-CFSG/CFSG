module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.OriginalG2
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.RemainingThree

/-!
# Applying the original G₂ exclusion after the component reduction

The original 14.7.52 producer supplies uniqueness of the original local and
the component property of its literal whole residual. These are exactly the
remaining placement hypotheses of the existing original 14.7.53 proof.
Consequently the Data constructor no longer requires a separate G₂ exclusion.

The genuine earlier component statement and the remaining original SL₃ row
stay explicit. No Data or G₂ geometry is assumed to obtain the exclusion.
Source: Aschbacher–Smith 14.7.52–53, printed pp.1065–1069,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.G2ResidualSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Apply the proved G₂ exclusion to the actual original residual selected
by 14.7.52, with its uniqueness and component hypotheses constructed. -/
theorem source_14_7_53_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L) :
    ¬ G2Residual F := by
  obtain ⟨hu,hC,_,_,_⟩ := source_14_7_52_at d h hab structural previous faithful
    earlier source47 exclusions
  exact OriginalG2.source_not_g2_residual_at h hab hu hC structural faithful

/-- The completed A₇, A₆, SL₄, SL₅ and original G₂ proofs feed Data.
Only the original SL₃ row and the genuine earlier source interfaces remain. -/
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
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(3,ZMod 2))) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  have hrows := EightSource.row_exclusions_of_linear_three_at d h hab structural
    previous faithful earlier source47 linearThree
  exact EightSource.exists_data_of_linear_three_at d h hab structural previous faithful
    earlier source47 linearThree
    (source_14_7_53_at d h hab structural previous faithful earlier source47 hrows)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.G2ResidualSource
