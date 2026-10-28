module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Assembly

/-!
# The guarded original component-to-Rudvalis application

The same original G,T,L,V and flag supply every source premise. Under the
multiple-overgroup guard, component classification and row exclusions give
14.7.52, whose literal residual alternatives construct Data by the proved
natural A₅ recognition. The independently proved original-module endgame
consumes this very datum and gives the concrete Rudvalis isomorphism.

Earlier14747, RowExclusions, the G₂ exclusion and genuine earlier structural,
faithful, 14.7.10 and original A₅-module inputs retain their existing producers.
This conditional implication does not assert their final discharge or the
unconditional classification. No universal structural record is inferred.
Source: Aschbacher–Smith 14.7.47–52, pp.1063–1065, and 14.7.63–75,
pp.1068–1078, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section03.SourceCompletion
open SourceEndgame.SourceAssembly.FullSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original caller's guarded source inputs construct the literal Data;
natural recognition is discharged by its same-G,T theorem. -/
theorem exists_data_of_component_statement_of_many_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) :=
  exists_data_of_component_statement_at d h hab (structural hmany) (previous hmany)
    faithful earlier source47 exclusions h53

/-- Apply the original 14.7.63–75 endgame to the Data just constructed from
14.7.47 and the component-row exclusions, on the same original ambient group. -/
theorem rudvalis_of_component_statement_of_many_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (h53 : ¬ G2Residual F)
    (five : OriginalAlternatingFiveModules1332At T L) :
    Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W, add, mod, ⟨datum⟩⟩ := exists_data_of_component_statement_of_many_at
    d h hab hmany structural previous faithful earlier source47 exclusions h53
  exact source_rudvalis_from_original_modules_at datum (structural hmany) faithful five

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
