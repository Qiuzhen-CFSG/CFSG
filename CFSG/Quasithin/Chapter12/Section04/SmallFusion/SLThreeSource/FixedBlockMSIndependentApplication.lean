module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockMSIndependent
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProducts
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockAssembly
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionAssembly

/-!
# Both original 12.4.6 consumers without a universal MS classifier

The independently proved fifth alternative identifies the whole original
MS commutator core with V and retains the quotient marking. The existing
kernel-action and residual calculations then give both centralizer products
before the fixed/moving split. The same marking supplies IsLinearTwoBlock
for the moving branch.

These results discharge exactly FixedBlockCalculation and
MovingLinearBlockCalculation. They feed the unchanged fixed-residual
assembly and corrected moving-residual assembly, retaining the independent
fixed action, moving centralizing-line and moving inverter inputs. No
normalization of L₁ by N_G(R) is assumed in either shared source conclusion.
The full binary MS classifier and other consumers remain independent.

Source: Aschbacher--Smith 12.4.6, printed p.814; C.1.34(5), pp.136--137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The two literal products on C_T(V) and C_R(L₁), before any fixed/moving split. -/
theorem fixedBlockIdentities_without_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    FixedBlockIdentities d := by
  obtain ⟨e,hc,hQ,_⟩ := d.ms_specialization_without_binary h structural marked hmodel hne hescape
  exact d.ms_fixedBlockIdentities h structural marked hmodel hne hescape e hc hQ

/-- The original moving-residual contradiction uses the independently proved
block and retains precisely its two separate action calculations. -/
theorem false_of_moving_without_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨_,_,_,hb⟩ := d.ms_specialization_without_binary h structural marked hmodel hne hescape
  exact d.false_of_moving_source_action h structural marked hmodel hne hescape hmoves
    hb hline hinv

end LocalGeometry

/-- The exact shared product contract with only its original Section 12.2 inputs. -/
theorem fixedBlockCalculation_without_binary
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) : FixedBlockCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape
  exact d.fixedBlockIdentities_without_binary h structural marked hmodel hne hescape

/-- The exact shared block contract used by the moving-residual assembly. -/
theorem movingLinearBlockCalculation_without_binary
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    MovingLinearBlockCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape
  obtain ⟨_,_,_,hb⟩ := d.ms_specialization_without_binary h structural marked hmodel hne hescape
  exact hb

/-- Apply the products to the existing fixed-residual consumer, retaining
its independent B.4.8 action calculation. -/
theorem fixedResidualCalculation_without_binary_and_action
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (action : FixedBlockActionCalculation.{u}) : FixedResidualCalculation.{u} :=
  fixedResidualCalculation_of_block_and_action structural marked
    (fixedBlockCalculation_without_binary structural marked) action

/-- Apply the original block to the corrected moving-residual consumer,
retaining its independent centralizing-line and inverter calculations. -/
theorem movingResidualCalculation_without_binary_and_actions
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (line : MovingCentralizingLineCalculation.{u})
    (inverter : MovingInverterCalculation.{u}) : MovingResidualCalculation.{u} :=
  movingResidualCalculation_of_action_sources structural marked
    (movingLinearBlockCalculation_without_binary structural marked) line inverter

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
