module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationBlock
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionAssembly

/-!
# Conditional specialization of the universal binary MS theorem

The actual MS group is LR=LT, with Sylow subgroup T. Once the proper
odd-index radical witness is supplied, the original source hypotheses give
all clauses of SmallMSPair. The universal binary C.1.34 implication then
selects its fifth alternative and gives the intrinsic natural binary-three
block, retaining the literal quotient and conjugation marking.

The final theorem applies that block to the existing moving-residual
consumer. The odd-index witness is still explicit here; this module does
not claim the full 12.4.6 specialization or its two centralizer products.

Source: Aschbacher--Smith C.1.31--34, pp.135--137, and 12.4.6, p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u

/-- Exactly the universal binary clause used by EarlierMSClassifications.of_binary.
It contains all five alternatives, and no source-specialized product assumption. -/
def BinaryMSClassification : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
    SmallMSPair KnownSimple.IsKnownSimple L R →
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives L R S 1 (ZMod 2) e

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The fifth alternative on the original subgroups, including the actual block.
The remaining local input is precisely MS2(a), not a Sylow assertion about R. -/
theorem ms_specialization_of_oddIndex
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hradical : MSOddIndex L d.R) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧ ChapterC.IsLinearTwoBlock L 3 := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hMS := smallMSPair_of_oddIndex h structural ext d hescape hradical
  obtain ⟨e,he⟩ := binary G L d.R hMS ⟨ext.quotientEquiv⟩ T
    (d.ms_sylow ext h hTV) inf_le_left
  obtain ⟨hc,hQ⟩ := d.ms_fixed_alternative h structural marked hmodel hne hescape e he
  exact ⟨e,hc,hQ,d.ms_isLinearTwoBlock h ext hmodel e hc hQ⟩

/-- The marked block discharges the original moving consumer's C.1.10 input.
The two independent quotient-action calculations remain the consumer's inputs. -/
theorem false_of_moving_ms_of_oddIndex
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hradical : MSOddIndex L d.R)
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨_,_,_,hb⟩ := d.ms_specialization_of_oddIndex h structural marked binary
    hmodel hne hescape hradical
  exact d.false_of_moving_source_action h structural marked hmodel hne hescape hmoves
    hb hline hinv

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
