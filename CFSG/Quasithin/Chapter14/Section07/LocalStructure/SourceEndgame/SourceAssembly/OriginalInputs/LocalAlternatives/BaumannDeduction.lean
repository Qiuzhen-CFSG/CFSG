module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.OriginalBaumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ChiefBound

/-!
# The 14.7.10 deduction in the original Rudvalis application

The independent binary MS classifier now implies the exact universal
Earlier14710 statement. On the original Data, its chief-count bound
contradicts the constructed four noncentral factors in the literal L₁,
giving N_G(Baum(R₁)) ≤ N_G(L). The same universal theorem supplies the
Baumann input of both OriginalInputs and LocalAlternatives, yielding their
actual Rudvalis isomorphism and D-model conclusions.

The classifier retains producer qt-rank-two-ms93. Structural1222 and the
original module/classification sources retain their existing producers;
qt-d-14775-source owns their final discharge and full Rudvalis assembly.
No chief bound, centralizer-core identity, or normalizer conclusion is assumed.

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
theorem baumann_normalizer_of_binary (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (binary : BinaryMSClassification KnownSimple.IsKnownSimple.{u}) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra escape
  let := seed_normal d.natural structural
  let := seed_elementary d.natural
  obtain ⟨a,_,⟨hi⟩,s,h0,h1,hs⟩ := baumann_ms_countercase d structural modules escape
  have hb := chief_count_le_of_msInput d.natural structural binary F a hi s h0 h1
  omega

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (binary : BinaryMSClassification KnownSimple.IsKnownSimple.{u})
include d structural faithful modules binary

/-- The literal OriginalInputs consumer with its universal Baumann input proved
from the independent binary classifier. -/
theorem source_rudvalis_of_binary_earlier_inputs (weakClosure : Theorem14731.{u})
    (localClassification : FixedComponentClassification d) :
    Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_earlier_inputs d structural faithful modules
    (earlier14710_of_binary structural binary) weakClosure localClassification

/-- The actual LocalAlternatives application, including the proved 14.7.31.
Only the earlier structural, faithful, module and MS classification inputs and
the actual local C.2.7 alternatives remain with their existing producers. -/
theorem source_rudvalis_of_binary_local_alternatives
    (alternatives : FixedComponentAlternatives d) : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_local_alternatives_source14731 d structural faithful modules
    (earlier14710_of_binary structural binary) alternatives

/-- The same Rudvalis isomorphism supplies the literal final D-model consumer. -/
theorem source_theoremDModel_of_binary_local_alternatives
    (alternatives : FixedComponentAlternatives d) : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_local_alternatives_source14731 d structural faithful modules
    (earlier14710_of_binary structural binary) alternatives

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
