module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Structure
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The central three-part of the actual lifted component

Noncentrality of O₃(G), together with the proved image formula for the
prepared cover, makes its three-core nontrivial. Its first omega subgroup
is nontrivial and is precisely the embedded center of the component lift.
Consequently three divides that center's order.

The literal restriction of the cover projection is a perfect central cover
of L. If L is identified with a centerless model whose perfect-cover kernels
have no three-part, that same projection gives a contradiction. The general
kernel statement is exposed solely as a remaining intrinsic model obligation;
no assertion about the multipliers of A₈ or G₂(2)′ is made here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.2 and
the proof of B.5.7, printed pp.103–106; I.1.1 and I.1.3, printed p.407.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
universe u w
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Noncentrality of the image forces a nontrivial three-core in this cover. -/
theorem lift_threeCore_ne_bot {L : Subgroup G} (d : NoncentralContext K G L) :
    pCore 3 d.cover.Cover ≠ ⊥ := by
  intro hb
  apply d.noncentral
  have hi := d.cover.map_pCore 3
  rw [hb, Subgroup.map_bot] at hi
  rw [← hi]
  exact bot_le

/-- The actual lifted component has center divisible by three. -/
theorem three_dvd_lift_center {L : Subgroup G} (d : NoncentralContext K G L) :
    3 ∣ Nat.card (center d.lift) := by
  have hp := (pCore_isPGroup (p := 3) (G := d.cover.Cover)).card_eq_or_dvd
  have h3 : 3 ∣ Nat.card (pCore 3 d.cover.Cover) := hp.resolve_left
    (fun h => lift_threeCore_ne_bot d ((eq_bot_iff_card _).mpr h))
  have hn := omega₁_map_subtype_ne_bot (pCore 3 d.cover.Cover) 3 h3
  rw [d.omega] at hn
  have hle : (center d.lift).map d.lift.subtype ≤ pCore 3 d.cover.Cover := by
    rw [← d.omega]
    exact map_subtype_le _
  have hpz : IsPGroup 3 (center d.lift) :=
    (pCore_isPGroup.to_le hle).of_injective
      ((center d.lift).equivMapOfInjective d.lift.subtype d.lift.subtype_injective).toMonoidHom
      ((center d.lift).equivMapOfInjective d.lift.subtype d.lift.subtype_injective).injective
  exact hpz.card_eq_or_dvd.resolve_left (fun h => hn (by
    rw [(eq_bot_iff_card _).mpr h, Subgroup.map_bot]))

/-- Restrict the original cover projection to its actual component. -/
noncomputable def componentCover {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) : PerfectCentralCovering.Cover d.lift L := by
  let := hL.2
  let := d.component.2
  let e := MulEquiv.subgroupCongr d.component_image
  let f : Theory.GroupTheory.Covering d.lift L := {
    toMonoidHom := e.toMonoidHom.comp (d.cover.projection.subgroupMap d.lift)
    surjective := e.surjective.comp (d.cover.projection.subgroupMap_surjective d.lift) }
  exact PerfectCentralCovering.ofCovering f

/-- The remaining intrinsic model fact, for the literal perfect central-cover kernel.
This is a proof obligation, not an earlier-source classification input. -/
def ThreeFreePerfectKernels (M : Type w) [Group M] : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (f : PerfectCentralCovering.Cover E M),
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker

/-- A centerless model with no three-part in perfect-cover kernels cannot be this L. -/
theorem not_model_of_threeFreePerfectKernels {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) {M : Type w} [Group M]
    (hz : center M = ⊥) (hf : ThreeFreePerfectKernels.{u} M) (e : L ≃* M) : False := by
  let c := componentCover hL d
  let f : PerfectCentralCovering.Cover d.lift M := {
    toMonoidHom := e.toMonoidHom.comp c.toMonoidHom
    surjective := e.surjective.comp c.surjective
    isPerfect := c.isPerfect
    ker_le_center := by
      intro x hx
      apply c.ker_le_center
      exact e.injective (hx.trans e.map_one.symm) }
  have hk : f.toMonoidHom.ker = center d.lift := by
    have hc := f.comap_center
    rwa [hz, MonoidHom.comap_bot] at hc
  apply hf d.lift f
  rw [hk]
  exact three_dvd_lift_center d



end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
