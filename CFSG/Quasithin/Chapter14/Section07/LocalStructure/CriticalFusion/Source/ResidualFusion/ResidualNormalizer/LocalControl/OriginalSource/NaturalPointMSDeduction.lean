module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMSApplication
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMSChiefBound

/-!
# The natural-point 14.7.10 theorem in the original Rudvalis application

The natural-point source theorem and the established chief-count argument
prove the exact universal Earlier14710 input. On the original Data, the
upper bound of three contradicts the constructed four noncentral factors
in the literal point residual, giving the Baumann normalizer containment.
The same universal theorem feeds the original Rudvalis isomorphism and the
full D-model conclusion through their existing source consumers.

Structural1222, faithful classification, the original module theorem and
local alternatives retain their independent producers. No binary MS
classifier or extra whole-core fixed-factor or centrality premise is added.
All earlier public APIs and the final classification endpoint are preserved.

Source: Aschbacher--Smith C.1.37, pp.141--143; 14.7.10, p.1045;
14.7.67(4), p.1070; and 14.7.75, pp.1077--1078.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Chapter12.Section08 CriticalFusion.Source
open ResidualNormalizer.LocalControl.OriginalSource
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The constructed four chief factors exclude the small-core branch on the
original Rudvalis datum, giving the literal Baumann normalizer containment. -/
theorem baumann_normalizer_of_naturalPointMS (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra escape
  let := seed_normal d.natural structural
  let := seed_elementary d.natural
  obtain ⟨a,_,⟨hi⟩,s,h0,h1,hs⟩ := baumann_ms_countercase d structural modules escape
  have hb := chief_count_le_of_naturalPointMS d.natural structural F a hi s h0 h1
  omega

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
include d structural faithful modules

/-- The literal OriginalInputs consumer with its universal Baumann input proved
by the natural-point source theorem. -/
theorem source_rudvalis_of_naturalPointMS_earlier_inputs (weakClosure : Theorem14731.{u})
    (localClassification : FixedComponentClassification d) :
    Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_earlier_inputs d structural faithful modules
    (earlier14710_of_naturalPointMS structural) weakClosure localClassification

/-- The actual LocalAlternatives application, including the proved 14.7.31.
Only the earlier structural, faithful, module inputs and
the actual local C.2.7 alternatives remain with their existing producers. -/
theorem source_rudvalis_of_naturalPointMS_local_alternatives
    (alternatives : FixedComponentAlternatives d) : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_local_alternatives_source14731 d structural faithful modules
    (earlier14710_of_naturalPointMS structural) alternatives

/-- The same Rudvalis isomorphism supplies the literal final D-model consumer. -/
theorem source_theoremDModel_of_naturalPointMS_local_alternatives
    (alternatives : FixedComponentAlternatives d) : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_local_alternatives_source14731 d structural faithful modules
    (earlier14710_of_naturalPointMS structural) alternatives

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
