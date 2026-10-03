module
public import Stellmacher.SectionNine.DistanceOneChiefOrdinaryKernel
public import Theory.GroupTheory.OddSubgroupLift

/-!
# Lifting a selected order-three chief actor

Any order-three subgroup of the canonical chief action range lifts to an
actual order-three subgroup D of the initial stabilizer. Its image under
the original chief projection is retained exactly, and Q_aD is the full
inverse image of the selected subgroup. Consequently any initial actor
normalizing the selected image normalizes Q_aD.

The preceding ordinary-kernel theorem identifies the projection kernel
with Q_a, a two-group. The general odd-subgroup lifting theorem applies
Schur–Zassenhaus inside the selected image's inverse image. Mapping the
lift to the graph group preserves its order and exact image. Normalizer
control follows from the elementary preimage and image normalizer laws.

This is the D* lift in Stellmacher (9.1), Journal of Algebra190 (1997),
p.48. The order-three image is a parameter supplied by the independent
comparison of the center and chief modules.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_three_actor_lift
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (Dbar : Subgroup (distanceOneChiefAction ctx.toLocalContext).range)
    (hDbar : Nat.card Dbar = 3) :
    let P := stabilizer ctx.Γ ctx.criticalPath.a
    let projection := (distanceOneChiefAction ctx.toLocalContext).rangeRestrict
    ∃ D : Subgroup G, D ≤ P ∧ Nat.card D = 3 ∧
      (D.subgroupOf P).map projection = Dbar ∧
      q ctx.Γ ctx.criticalPath.a ⊔ D = (Dbar.comap projection).map P.subtype ∧
      ∀ J : Subgroup G, J ≤ P →
        (J.subgroupOf P).map projection ≤ Subgroup.normalizer (Dbar : Set _) →
        J ≤ Subgroup.normalizer ((q ctx.Γ ctx.criticalPath.a ⊔ D : Subgroup G) : Set G) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let action : P →* MulAut (DistanceOneChiefQuotient ctx.toLocalContext) := distanceOneChiefAction ctx.toLocalContext
  change Subgroup action.range at Dbar
  change Nat.card Dbar = 3 at hDbar
  let projection := action.rangeRestrict
  let Q := q ctx.Γ ctx.criticalPath.a
  have hQP : Q ≤ P := by
    change q ctx.Γ ctx.criticalPath.a ≤ P
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hker : projection.ker = Q.subgroupOf P := by
    rw [MonoidHom.ker_rangeRestrict]
    exact distance_one_chief_ordinary_action_kernel ctx hb hfaith branch
  have hQp : IsPGroup 2 (Q.subgroupOf P) := by
    change IsPGroup 2 ((q ctx.Γ ctx.criticalPath.a).subgroupOf P)
    rw [q, ctx.Γ.twoCoreAt_def]
    change IsPGroup 2 (((pCore 2 P).map P.subtype).subgroupOf P)
    have heq : ((pCore 2 P).map P.subtype).subgroupOf P = pCore 2 P :=
      Subgroup.comap_map_eq_self (by simp)
    rw [heq]
    exact pCore_isPGroup
  obtain ⟨D0, hmap, hinj, hcard, hcover⟩ := projection.exists_odd_subgroup_lift
    action.rangeRestrict_surjective (hker ▸ hQp) Dbar (by rw [hDbar]; decide)
  let D := D0.map P.subtype
  have hDP : D ≤ P := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf P = D0 := Subgroup.comap_map_eq_self (by simp)
  have hcoverG : Q ⊔ D = (Dbar.comap projection).map P.subtype := by
    have hh := congrArg (Subgroup.map P.subtype) hcover
    rw [Subgroup.map_sup, hker, Subgroup.map_subgroupOf_eq_of_le hQP] at hh
    exact hh
  refine ⟨D, hDP, ?_, ?_, hcoverG, ?_⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hcard, hDbar]
  · rw [hDsub]
    exact hmap
  · intro J hJP hJ
    change J ≤ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G)
    rw [hcoverG]
    have hnative : J.subgroupOf P ≤ Subgroup.normalizer (Dbar.comap projection : Set P) :=
      ((Subgroup.map_le_iff_le_comap).mp hJ).trans (Subgroup.le_normalizer_comap (H := Dbar) projection)
    have hm := Subgroup.map_mono (f := P.subtype) hnative
    rw [Subgroup.map_subgroupOf_eq_of_le hJP] at hm
    exact hm.trans (Subgroup.le_normalizer_map (H := Dbar.comap projection) P.subtype)
end Stellmacher.SectionNine
