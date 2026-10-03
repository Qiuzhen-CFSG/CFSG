module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# The middle center lies in the middle residual core

In the actual Section Ten configuration, the middle four-center is its full
commutator with the middle two-residual. It consequently lies in that residual's
two-core, whose center has at least four elements. No small-module case or
extra local model is assumed.

The initial-center full-residual theorem has no critical-length-one premise.
Conjugation along the actual middle orbit transports that theorem, preserving
both the center and the local residual. The middle center lies in the middle
two-core, so the standard residual/core commutator bound gives the asserted
containment. The center also lies in the center of the middle two-core; its
inclusion therefore embeds four elements into the residual core's center.

This supplies the center input to the C4×C4 recognition in Stellmacher
(10.1)(a1), printed p.60/PDF p.50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_middle_center_full_residual
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ⁅ZAt ctx.Γ middle, EAt ctx.Γ middle⁆ = ZAt ctx.Γ middle := by
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hh := congrArg (Subgroup.map (MulAut.conj actor⁻¹).toMonoidHom)
    (distance_one_initial_center_full_residual ctx.toLocalContext.toSectionNineLocalContext)
  let f := (MulAut.conj actor⁻¹).toMonoidHom
  have hPmap : (GAt ctx.Γ ctx.criticalPath.a).map f = GAt ctx.Γ middle :=
    (stabilizer_act ctx.Γ actor ctx.criticalPath.a).symm.trans (congrArg _ hactor)
  have hZmap : (ZAt ctx.Γ ctx.criticalPath.a).map f = ZAt ctx.Γ middle := by
    change (z ctx.Γ ctx.criticalPath.a).map f = z ctx.Γ middle
    rw [← z_act, hactor]
  have hEmap : (EAt ctx.Γ ctx.criticalPath.a).map f = EAt ctx.Γ middle := by
    change (ctx.Γ.twoResidualAt ctx.criticalPath.a).map f = ctx.Γ.twoResidualAt middle
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoResidualAt_def]
    exact map_twoResidualAmbient_of_subgroup_image (GAt ctx.Γ ctx.criticalPath.a) f
      (GAt ctx.Γ middle) hPmap
  change (⁅ZAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆).map f =
    (ZAt ctx.Γ ctx.criticalPath.a).map f at hh
  rw [Subgroup.map_commutator, hZmap, hEmap] at hh
  exact hh

public theorem ten_one_middle_center_le_residual_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ZAt ctx.Γ middle ≤ twoCoreIn (EAt ctx.Γ middle) := by
  let P := GAt ctx.Γ middle
  have hZQ : ZAt ctx.Γ middle ≤ QAt ctx.Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  rw [← ten_one_middle_center_full_residual ctx middle hpath]
  apply (Subgroup.commutator_mono hZQ le_rfl).trans
  rw [Subgroup.commutator_comm]
  change ⁅ctx.Γ.twoResidualAt middle, ctx.Γ.twoCoreAt middle⁆ ≤
    twoCoreIn (ctx.Γ.twoResidualAt middle)
  rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def]
  exact residual_commutator_core_le P
public theorem ten_one_middle_residual_center_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    4 ≤ Nat.card (Subgroup.center (twoCoreIn (EAt ctx.Γ middle))) := by
  let Z := ZAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let D := twoCoreIn (EAt ctx.Γ middle)
  have hZD : Z ≤ D := ten_one_middle_center_le_residual_core ctx middle hpath
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hZcentral : Z ≤ Subgroup.centralizer (D : Set G) := by
    rw [show Z = omegaOneCenter Q from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact ((omegaOneCenter_le_centerAmbient Q).trans (centerAmbient_le_centralizer Q)).trans
      (Subgroup.centralizer_le hDQ)
  let inclusion : Z → Subgroup.center D := fun z =>
    ⟨⟨z, hZD z.property⟩, Subgroup.mem_center_iff.mpr (fun d =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZcentral z.property) d d.property))⟩
  have hinjective : Function.Injective inclusion := by
    intro z w heq
    exact Subtype.ext (congrArg (fun x : Subgroup.center D => ((x : D) : G)) heq)
  have hcard := Nat.card_le_card_of_injective inclusion hinjective
  rw [show Nat.card Z = 4 from (sectionTenOpeningData ctx middle hpath).center_card] at hcard
  exact hcard
end Stellmacher.SectionTen
