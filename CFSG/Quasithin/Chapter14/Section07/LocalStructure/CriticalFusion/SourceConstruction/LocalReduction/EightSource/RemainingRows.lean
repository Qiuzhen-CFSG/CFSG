module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Assembly

/-!
# Original local reduction with only the two remaining linear rows

The original A₇, A₆ and SL₅(2) exclusions now supply their own source
proofs. The row-exclusion family and the original Data constructor therefore
require only the independent SL₃(2) and SL₄(2) exclusions. The latter still
needs the full noncentral-kernel argument. The separate G₂ exclusion and
genuine earlier source hypotheses remain explicit in the Data consumer.

Source: Aschbacher--Smith 14.7.49--52 and 14.7.63, pp.1064--1065,1069.
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

/-- Only SL₃(2) and SL₄(2) remain in the actual row-exclusion family. -/
theorem row_exclusions_of_linear_three_four_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (linearRows : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        ∀ n : ℕ, (n = 3 ∨ n = 4) →
          ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(n,ZMod 2))) :
    RowExclusions F L := by
  apply AlternatingSevenSource.row_exclusions_of_other_rows_at
    d h hab structural previous faithful earlier source47
  intro I hI C hC
  refine ⟨?_,source_14_7_49_alternating_six_at d h hab structural previous faithful
    earlier source47 I hI C hC⟩
  intro n hlo hhi
  have hn : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hn with rfl | rfl | rfl
  · exact linearRows I hI C hC 3 (Or.inl rfl)
  · exact linearRows I hI C hC 4 (Or.inr rfl)
  · exact source_14_7_51_linear_five_at d h hab structural previous faithful
      earlier source47 I hI C hC

/-- Apply the completed named rows to the original Data constructor.
The two remaining linear exclusions and independent G₂ duty are explicit. -/
theorem exists_data_of_linear_three_four_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (linearRows : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        ∀ n : ℕ, (n = 3 ∨ n = 4) →
          ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(n,ZMod 2)))
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_component_statement_at d h hab structural previous faithful earlier
    source47 (row_exclusions_of_linear_three_four_at d h hab structural previous faithful
      earlier source47 linearRows) h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
