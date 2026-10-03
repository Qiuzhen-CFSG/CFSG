module
public import Stellmacher.SectionOne.OneSevenSylowInvariantFixed
public import Stellmacher.SectionEight.EightFourSmallRankAction

/-!
# Invariant-subgroup control for the original initial-center witness

The original faithful quotient action satisfies the canonical Sylow
invariant-subgroup criterion. A subgroup of the initial center normalized
by the distinguished Sylow therefore contains the original J-fixed
subgroup as soon as its order is at least the fixed subgroup's order.
All generation, unique-maximality, and residual-fixed-space inputs are
derived from the actual local Section Eight context, with the supplied witness
unchanged. The canonical theorem remains an exact wrapper. Thus the same
argument also applies to the generated group's original graph without
assuming that it inherits the ambient Hypothesis Two.

The residual image and Sylow image generate the faithful quotient; the
residual has no fixed vectors and the Sylow image is maximal. The abstract
Sylow invariant-subgroup criterion therefore applies to the actual restricted
subgroup, and mapping back through the original witness gives the inclusion.
This adapter is used at the transported edge in the last paragraph of
Stellmacher (8.4), printed p.40 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_sylow_invariant_contains_fixed_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (invariant : Subgroup H) (hle : invariant ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hnormalize : S ≤ Subgroup.normalizer (invariant : Set H))
    (hcard : Nat.card (w.oneJFixedPoints S) ≤ Nat.card invariant) :
    w.oneJFixedPoints S ≤ invariant := by
  classical
  let hyp := ctx.sectionSeven
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let moduleGroup := ZAt graph path.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom moduleGroup w.action
  let image := (S.subgroupOf initial).map w.projection
  let residual := SectionOne.oneE (V := moduleGroup) image
  have hneighbor : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph hneighbor
  have hlocal := (local_quotient_sylow_action_setup hyp graph path w).1
  obtain ⟨hSylowLe, nativeSylow, hnativeSylow⟩ :=
    (SevenSix.edge_sylow_data hyp graph path).1
  have hnative : (nativeSylow : Subgroup initial) = S.subgroupOf initial := by
    apply Subgroup.map_injective initial.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSylowLe]
    exact hnativeSylow
  let imageSylow := nativeSylow.mapSurjective w.surjective
  have himage : (imageSylow : Subgroup w.X) = image := by
    change (nativeSylow : Subgroup initial).map w.projection = _
    rw [hnative]
  have hresidual := lemma_eight_one_residual_join_local ctx w
  have hresidualLe : EAt graph path.a ≤ initial := by
    rw [show EAt graph path.a = twoResidualAmbient initial from
      graph.twoResidualAt_def path.a]
    exact Subgroup.map_subtype_le _
  have hresidualImage : ((EAt graph path.a).subgroupOf initial).map w.projection ≤
      residual := by
    rw [show residual = _ from hresidual]
    exact le_sup_left
  have hgeneration : residual ⊔ image = ⊤ := by
    have hnativeGen : (EAt graph path.a).subgroupOf initial ⊔
        S.subgroupOf initial = ⊤ := by
      apply Subgroup.map_injective initial.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hresidualLe,
        Subgroup.map_subgroupOf_eq_of_le hSylowLe, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      rw [show EAt graph path.a = twoResidualAmbient initial from
        graph.twoResidualAt_def path.a]
      exact SectionThree.twoResidual_sup_sylowImage ⟨nativeSylow, hnativeSylow⟩
    have hmap := congrArg (Subgroup.map w.projection) hnativeGen
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ w.surjective] at hmap
    exact top_unique (hmap.ge.trans (sup_le_sup_right hresidualImage image))
  have hfixed : FixedPoints.subgroup residual moduleGroup = ⊥ := by
    apply le_bot_iff.mp
    intro point hpoint
    have hpointFixed : point ∈ FixedPoints.subgroup
        (((EAt graph path.a).subgroupOf initial).map w.projection) moduleGroup :=
      fun actor => hpoint ⟨actor, hresidualImage actor.property⟩
    have hmap := Subgroup.mem_map_of_mem moduleGroup.subtype hpointFixed
    have hzero : moduleGroup ⊓ Subgroup.centralizer (EAt graph path.a : Set H) = ⊥ :=
      eight_four_initial_residual_center_trivial_local ctx hcenter
    rw [w.fixedPoints_map_subtype (EAt graph path.a) hresidualLe, hzero] at hmap
    exact Subtype.ext hmap
  have hcoatom : IsCoatom image := eight_four_faithful_sylow_isCoatom_local ctx w
  have hunique : IsUniqueMaximalContaining image (⊤ : Subgroup w.X) := by
    apply (uniqueMaximalContaining_top_iff image).mpr
    refine ⟨image, hcoatom, le_rfl, ?_⟩
    intro maximal hmaximal hle
    exact (hcoatom.le_iff_eq hmaximal.ne_top).mp hle
  let submodule := invariant.subgroupOf moduleGroup
  have hstable : ∀ actor : imageSylow, ∀ vector ∈ submodule,
      actor • vector ∈ submodule := by
    intro actor vector hvector
    have hactor : (actor : w.X) ∈ image := himage ▸ actor.property
    obtain ⟨native, hnative, hprojection⟩ := hactor
    change ((w.action (actor : w.X)) vector : H) ∈ invariant
    rw [← hprojection, w.action_compatible]
    exact (Subgroup.mem_normalizer_iff.mp (hnormalize hnative) (vector : H)).mp hvector
  have hfixedCard : Nat.card (FixedPoints.subgroup
      (SectionOne.oneJ (V := moduleGroup) (imageSylow : Subgroup w.X)) moduleGroup) ≤
        Nat.card submodule := by
    rw [himage, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    change Nat.card ((FixedPoints.subgroup
      (SectionOne.oneJ (V := moduleGroup) image) moduleGroup).map moduleGroup.subtype) ≤
        Nat.card invariant at hcard
    rwa [Subgroup.card_map_of_injective moduleGroup.subtype_injective] at hcard
  have hcontains := SectionOne.oneSeven_sylow_invariant_contains_fixed_of_card_ge
    hlocal imageSylow (by rw [himage]; exact hgeneration)
      (by rw [himage]; exact hunique) (by rw [himage]; exact hfixed)
      submodule hstable hfixedCard
  rw [himage] at hcontains
  have hmap := Subgroup.map_mono (f := moduleGroup.subtype) hcontains
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmap
  exact hmap

public theorem eight_four_sylow_invariant_contains_fixed
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (invariant : Subgroup H) (hle : invariant ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hnormalize : S ≤ Subgroup.normalizer (invariant : Set H))
    (hcard : Nat.card (w.oneJFixedPoints S) ≤ Nat.card invariant) :
    w.oneJFixedPoints S ≤ invariant :=
  eight_four_sylow_invariant_contains_fixed_local ctx.toLocalContext hcenter w
    invariant hle hnormalize hcard

end Stellmacher.SectionEight
