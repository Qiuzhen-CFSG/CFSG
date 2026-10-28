module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionSpan
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionResidual
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FusionInput

/-!
# Assembly of the corrected moving-residual source contradiction

The canonical N_G(R)-invariant span supplies the elementary nine quotient.
The original centralizing action kernel supplies X₁, its relative normality
and centralization of L. An actor in T∩L fixes the X₁ line, so inversion on
the L₁ line makes the two lines distinct. These constructions feed the
normal-residual orbit and characteristic-two uniqueness contradiction.

Two independent source action calculations remain explicit: the centralizing
image has order three, and an element of T∩L inverts the other quotient line.
The linear block marking remains with the existing C.1.34 specialization.
Only after the conditional contradiction is proved do we recover the old
MovingResidualCalculation API by false elimination. The unrestricted cubic
family and its existing consumer interfaces are unchanged.

The final adapter applies this to the original Chapter14 fusion input.
Source: Aschbacher–Smith, proof of 12.4.6, printed p.814, and 12.4.7.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- A source actor in T∩L, on the literal moving-span quotient. -/
def MovingLineInverter (d : LocalGeometry D) : Prop :=
  ∃ t : T, (t : G) ∈ L ∧
    ∀ z ∈ normalCubicResidualImage d.movingSpan d.L₁,
      normalCubicQuotientAction d.movingSpan
        ⟨t, d.normalizer_normalizes_movingSpan (d.sylow_normalizes t.property)⟩ z = z⁻¹

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Construction of the corrected geometry from the two remaining marked
local action facts. All other fields are proved on the original subgroups. -/
theorem normalResidualGeometry_of_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hblock : ChapterC.IsLinearTwoBlock L 3)
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : Nonempty (NormalResidualGeometry d) := by
  obtain ⟨hel, h9⟩ := d.movingSpan_quotient h structural marked hmodel hne hescape hmoves
  let := hel
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  have hTM := (structural G T L h).1
  have hTX := d.sylow_normalizes.trans d.normalizer_normalizes_movingSpan
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hL1 : d.L₁ ∈ normalCubicResiduals d.movingSpan := by
    refine ⟨d.lineResidual_le_movingSpan, ?_, d.lineResidual_twoPerfect, ?_⟩
    · apply normal_subgroupOf_of_le_normalizer
      exact (le_inf hXM (d.movingSpan_le_centralizer hNE)).trans
        d.centralizer_normalizes_lineResidual
    · exact d.lineResidual_quotient_card ext hne
        (d.fixed_le_plane h structural marked hmodel hne hescape)
  have hX1 := centralizingResidual_mem L d.movingSpan h9 hline
  obtain ⟨t, htL, htinv⟩ := hinv
  let a : normalizer (d.movingSpan : Set G) :=
    ⟨t, d.normalizer_normalizes_movingSpan (d.sylow_normalizes t.property)⟩
  have htfix : ∀ z ∈ normalCubicResidualImage d.movingSpan (centralizingResidual L d.movingSpan),
      normalCubicQuotientAction d.movingSpan a z = z := by
    apply quotientAction_fixes_of_centralizes
    exact le_centralizer_iff.mp (centralizingResidual_centralizes L d.movingSpan hblock hXM) htL
  refine ⟨{
    X := d.movingSpan
    X₁ := centralizingResidual L d.movingSpan
    normalizes_X := d.normalizer_normalizes_movingSpan
    elementary := hel
    quotient_card := h9
    line_mem := hL1
    fixed_mem := hX1
    distinct_images := ?_
    actor := t
    inverts_line := htinv
    fixes_line := htfix
    characteristic_two := moving_overgroup_characteristicTwo h structural d.movingSpan hXM
    residual_normal := centralizingResidual_normal_join L d.movingSpan T hblock hXM hTM hTX
    residual_nontrivial := centralizingResidual_ne_bot L d.movingSpan h9 hline }⟩
  exact cubic_images_distinct_of_inverted_fixed _ _ (normalCubicResidualImage_card hL1)
    (normalCubicQuotientAction d.movingSpan a) htinv htfix

/-- The genuine moving-branch contradiction, conditional only on the block
marking and the two isolated source-action calculations. -/
theorem false_of_moving_source_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hblock : ChapterC.IsLinearTwoBlock L 3)
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨f⟩ := d.normalResidualGeometry_of_action h structural marked hmodel hne
    hescape hmoves hblock hline hinv
  exact d.false_of_moving_normal_residual h structural marked hmodel hne hescape hmoves f

end LocalGeometry

/-- The shared C.1.34(5) marking, to be discharged by the existing MS specialization owner. -/
def MovingLinearBlockCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    ChapterC.IsLinearTwoBlock L 3

/-- The order of the actual kernel's image, not of an unrelated abstract line. -/
def MovingCentralizingLineCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G) →
    Nat.card (centralizingLine L d.movingSpan) = 3

/-- The marked Sylow actor calculation, independent of the centralizing-line order. -/
def MovingInverterCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G) →
    MovingLineInverter d

/-- Preserve the old universal consumer API only after deriving the genuine
source contradiction. No unrestricted cubic-family count is asserted. -/
theorem movingResidualCalculation_of_action_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (block : MovingLinearBlockCalculation.{u})
    (line : MovingCentralizingLineCalculation.{u}) (inverter : MovingInverterCalculation.{u}) :
    MovingResidualCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape hmoves
  exact (d.false_of_moving_source_action h structural marked hmodel hne hescape hmoves
    (block G T L V h D hmodel hne d hescape)
    (line G T L V h D hmodel hne d hescape hmoves)
    (inverter G T L V h D hmodel hne d hescape hmoves)).elim

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

/-- Application to the existing Chapter14 consumer, with each remaining
source producer explicit and final discharge retained by the fusion owner. -/
theorem slThreeFusion1247_of_moving_action_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (block : MovingLinearBlockCalculation.{u})
    (line : MovingCentralizingLineCalculation.{u}) (inverter : MovingInverterCalculation.{u}) :
    SLThreeFusion1247.{u} :=
  slThreeFusion1247_of_calculations structural marked localFacts fixed
    (movingResidualCalculation_of_action_sources structural marked block line inverter)

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
