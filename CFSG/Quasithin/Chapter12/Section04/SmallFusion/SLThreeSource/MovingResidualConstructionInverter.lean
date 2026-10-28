module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionAssembly
public import Theory.SpecificGroups.PSL3Two.Parabolics.CoveredResidualCommutator
public import Theory.GroupTheory.PResidual.NormalCubicInverter

/-!
# The source Sylow inverter on the moving residual line

The actual intersection T∩L is Sylow in L. In the marked quotient
L/O₂(L) ≅ SL₃(2), the image of L₁ is a Sylow-normalized cubic residual,
so its Sylow commutators generate that image. Thus [L₁,T∩L] is not a
two-group. Relative normality of L₁ in the canonical moving span X then
forces an actor in T∩L to invert its literal image in X/O₂(X).

This discharges `MovingInverterCalculation` without a centralizing-line
cardinality or block-marking premise. The final adapters feed the existing
moving-residual and Chapter14 fusion consumers; their other source inputs
remain with their respective owners.

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814, the choice of
an inverting element in T∩L; the final fusion application is 12.4.7.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

private theorem component_sylow (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hTL)
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (L.subgroupOf J)
  let e := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup (L.subgroupOf J)).map e.toMonoidHom = _
  rw [hP]
  ext l
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hl
    exact ⟨⟨⟨l, (le_sup_left : L ≤ J) l.property⟩, l.property⟩, hl, rfl⟩

/-- An actor in the original T∩L inverts the actual moving residual image. -/
theorem movingLineInverter
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MovingLineInverter d := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTL := (structural G T L h).1
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  have hc := d.lineResidual_quotient_card ext hne hFE
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  have hY : d.L₁ ∈ normalCubicResiduals d.movingSpan := by
    refine ⟨d.lineResidual_le_movingSpan, ?_, d.lineResidual_twoPerfect, hc⟩
    exact normal_subgroupOf_of_le_normalizer
      ((le_inf hXM (d.movingSpan_le_centralizer hNE)).trans d.centralizer_normalizes_lineResidual)
  have hTY : (T : Subgroup G) ≤ normalizer (d.L₁ : Set G) :=
    (le_inf hTL d.sylow_normalizes).trans (d.intersection_normalizes_lineResidual hNE)
  obtain ⟨S, hS⟩ := component_sylow hTL
  let A := d.L₁.subgroupOf L
  have hAL : d.L₁ ≤ L := d.lineResidual_le.trans inf_le_left
  let eA := subgroupOfEquivOfLe hAL
  have hAp : IsPPerfect 2 A := d.lineResidual_twoPerfect.of_surjective
    eA.symm.toMonoidHom eA.symm.surjective
  have hAc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).trans hc
  let f : L →* Matrix.PSL3Two.SL :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ext.quotientEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hSA : (S : Subgroup L) ≤ normalizer (A : Set L) := by
    rw [hS]
    intro t ht
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hTY ht) a
  have hn := Matrix.PSL3Two.ResidualRecognition.commutator_not_two_of_cover
    f hf hk A S hAp hAc hSA
  have hcomm : ¬ IsPGroup 2 (⁅d.L₁, (T : Subgroup G) ⊓ L⁆ : Subgroup G) := by
    intro hp
    apply hn
    have he : (⁅A, (S : Subgroup L)⁆).map L.subtype = ⁅d.L₁, (T : Subgroup G) ⊓ L⁆ := by
      rw [map_commutator, hS, map_subgroupOf_eq_of_le hAL, subgroupOf_map_subtype]
    have hm : IsPGroup 2 ((⁅A, (S : Subgroup L)⁆).map L.subtype) := he.symm ▸ hp
    exact hm.of_equiv ((⁅A, (S : Subgroup L)⁆).equivMapOfInjective
      L.subtype L.subtype_injective).symm
  obtain ⟨t, ht⟩ := exists_normalCubic_inverter_of_commutator_not_two
    d.movingSpan d.L₁ ((T : Subgroup G) ⊓ L) hY
    (inf_le_left.trans (d.sylow_normalizes.trans d.normalizer_normalizes_movingSpan))
    (inf_le_left.trans hTY) hcomm
  exact ⟨⟨t, t.property.1⟩, t.property.2, ht⟩

end LocalGeometry

/-- The exact source inverter callback, with both moving-branch escapes allowed. -/
theorem movingInverterCalculation
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    MovingInverterCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape _
  exact d.movingLineInverter h structural marked hmodel hne hescape

/-- Discharge the inverter premise of the existing moving-residual consumer. -/
theorem movingResidualCalculation_of_block_and_line
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (block : MovingLinearBlockCalculation.{u})
    (line : MovingCentralizingLineCalculation.{u}) : MovingResidualCalculation.{u} :=
  movingResidualCalculation_of_action_sources structural marked block line
    (movingInverterCalculation structural marked)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

/-- The literal fusion consumer with its inverter calculation discharged. -/
theorem slThreeFusion1247_of_block_and_line
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (block : MovingLinearBlockCalculation.{u})
    (line : MovingCentralizingLineCalculation.{u}) : SLThreeFusion1247.{u} :=
  slThreeFusion1247_of_moving_action_sources structural marked localFacts fixed block line
    (movingInverterCalculation structural marked)

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
