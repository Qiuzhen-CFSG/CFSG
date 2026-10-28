module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionLineActionAssembly
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationAssembly

/-!+# The moving branch of 12.4.6 from the earlier MS classification

The original MS specialization supplies the natural binary-three block.
The actual action on L/O₂(L) supplies the centralizing line in X/O₂(X),
and the Sylow intersection T∩L supplies its complementary line's inverter.
Together these give the corrected normal-residual geometry, whose orbit
and uniqueness argument contradicts both escaping-normalizer assumptions.

No local action, block-marking, residual-construction or counting premise
remains. The earlier universal binary C.1.34 classification is still explicit:
its producer is `qt-rank-two-ms93`. Final discharge of this premise in the
moving branch stays with `qt-d-1246-l3-moving-residuals`; the independent
local-plane, fixed-residual and commutator branches stay with the fusion and
fixed-space assembly owners. Structural1222 and SLThreeAlternative1222 are
the other authorized earlier source inputs.

The old MovingResidualCalculation interface is recovered only from the
genuine contradiction. The unrestricted cubic family is never counted.
The final adapters apply this result to the literal Chapter 14 consumers.

Source: Aschbacher--Smith, C.1.34(5), printed pp.136--137, and the proof of
12.4.6 and Lemma 12.4.7, printed p.814.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The moving-branch contradiction on the original source subgroups.
Only the earlier universal Section 12.2 and binary C.1.34 inputs remain. -/
theorem false_of_moving_source_of_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) : False := by
  exact d.false_of_moving_ms h structural marked binary hmodel hne hescape hmoves
    (d.centralizingLine_card h structural marked hmodel hne hescape hmoves)
    (d.movingLineInverter h structural marked hmodel hne hescape)

end LocalGeometry

/-- Preserve the existing consumer after proving the moving branch impossible.
All three local calculations have been supplied by their source producers. -/
theorem movingResidualCalculation_of_binary
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u}) : MovingResidualCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape hmoves
  exact (d.false_of_moving_source_of_binary h structural marked binary hmodel hne
    hescape hmoves).elim

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

/-- Discharge the moving-residual premise of the original fusion consumer.
The local-plane and fixed-residual branches remain with `qt-d-1242-l3-fusion-source`. -/
theorem slThreeFusion1247_of_binary_moving
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u}) :
    SLThreeFusion1247.{u} :=
  slThreeFusion1247_of_calculations structural marked localFacts fixed
    (movingResidualCalculation_of_binary structural marked binary)

/-- The same source implication at the literal fixed-space consumer.
Its independent commutator geometry remains explicit with that assembly owner. -/
theorem slThreeFixedSpace1242_of_binary_moving
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (geometry : SLThreeCommutator1242.{u}) : SLThreeFixedSpace1242.{u} :=
  slThreeFixedSpace1242_of_local_sources structural marked localFacts fixed
    (movingResidualCalculation_of_binary structural marked binary) geometry

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
