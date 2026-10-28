module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecialization
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationRadical
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProducts
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockAssembly

/-!
# The original fixed-line specialization of C.1.34

The proper plane normalizer supplies MS2(a) for LR = LT, with T as its
Sylow subgroup. The universal binary MS theorem and the original marked
indecomposable module select alternative (5) and identify [O₂(LR),L] = V.
The proved kernel and residual calculations then give both literal
centralizer products, before any split according to normalization of L₁.

The specialization also retains the intrinsic linear-three block, its
natural binary module model, and the exact quotient marking. These supply
the existing moving-residual consumer; the products supply the existing
fixed-residual consumer. No odd-index, selected-alternative, kernel-action
or centralizer-product premise remains.

Structural1222, SLThreeAlternative1222 and the universal binary C.1.34
implication are the authorized earlier inputs. The parent
`qt-d-1246-l3-fixed-block` retains discharge of C.1.34 through
`qt-rank-two-ms93`, and the independent fixed-branch action calculation.
The moving branch retains its two quotient-action calculations with
`qt-d-1246-l3-moving-residuals`.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and the shared
MS-pair paragraph in the proof of 12.4.6, printed pp.813--814.
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

/-- C.1.34(5) and the actual block on the original source subgroups.
The proper odd-index radical witness is constructed, not assumed. -/
theorem ms_specialization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧ ChapterC.IsLinearTwoBlock L 3 := by
  exact d.ms_specialization_of_oddIndex h structural marked binary hmodel hne hescape
    (d.ms_oddIndex h structural marked hmodel hne hescape)

/-- Retain the literal natural block model with its common C.1.34 quotient
marking, intrinsic shortness, and identification of U(L) with the original V. -/
theorem ms_markedBlock
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧
      ChapterC.IsShort L ∧ ChapterC.IsLinearTwoBlock L 3 ∧
      (ChapterC.blockU L).map L.subtype = V ∧
      ∃ b : ChapterC.BlockModuleModel L naturalBinaryThreeAction, b.quotientIso = e := by
  obtain ⟨e, hc, hQ, hb⟩ := d.ms_specialization h structural marked binary hmodel hne hescape
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  exact ⟨e, hc, hQ, d.ms_isShort h ext e hc hQ, hb, d.ms_blockU_eq hQ,
    d.ms_blockModel e hc hQ, d.ms_blockModel_quotientIso e hc hQ⟩

/-- Both products in the shared MS paragraph of 12.4.6, with no assumption
that N_G(R) normalizes the literal embedded residual L₁. -/
theorem fixedBlockIdentities_of_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    FixedBlockIdentities d := by
  obtain ⟨e, hc, hQ, _⟩ := d.ms_specialization h structural marked binary hmodel hne hescape
  exact d.ms_fixedBlockIdentities h structural marked hmodel hne hescape e hc hQ

/-- The shared block specialization supplies the existing moving-branch
consumer; only that branch's independent action calculations remain. -/
theorem false_of_moving_ms
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u})
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨_, _, _, hb⟩ := d.ms_specialization h structural marked binary hmodel hne hescape
  exact d.false_of_moving_source_action h structural marked hmodel hne hescape hmoves
    hb hline hinv

end LocalGeometry

/-- The exact universal fixed-block contract, conditional only on the
authorized earlier Section 12.2 implications and binary C.1.34. -/
theorem fixedBlockCalculation_of_binary
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u}) : FixedBlockCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape
  exact d.fixedBlockIdentities_of_binary h structural marked binary hmodel hne hescape

/-- The same specialization supplies the exact shared block interface used
by the original moving-residual assembly. -/
theorem movingLinearBlockCalculation_of_binary
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u}) : MovingLinearBlockCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape
  obtain ⟨_, _, _, hb⟩ := d.ms_specialization h structural marked binary hmodel hne hescape
  exact hb

/-- Apply the completed block calculation to the unchanged fixed-residual
assembly. The separate B.4.8 action input remains with its source owner. -/
theorem fixedResidualCalculation_of_binary_and_action
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (binary : BinaryMSClassification.{u}) (action : FixedBlockActionCalculation.{u}) :
    FixedResidualCalculation.{u} :=
  fixedResidualCalculation_of_block_and_action structural marked
    (fixedBlockCalculation_of_binary structural marked binary) action

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
