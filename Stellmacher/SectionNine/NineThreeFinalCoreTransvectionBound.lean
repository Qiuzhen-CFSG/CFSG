module

public import Stellmacher.SectionNine.NineThreeFinalCoreFrattiniDisplacement
public import Stellmacher.SectionNine.NineThreeMixedSylow

/-!
# The actual final core action has displacement at most two

In the normalized order-sixteen branch of Stellmacher (9.3), assume the
initial center intersects the actual mixed centralizer's two-core in a
subgroup of order at most four. The mixed commutator has order two and is
central in that centralizer. Killing its line in the core Frattini quotient
therefore leaves at most two displacement vectors for the initial-center
actor. The returned action is the original conjugation action, with kernel
exactly the two-core; its formula and elementary module are retained.

The proof transports the ambient intersection and commutator containment
through the literal centralizer inclusion, then applies kernel-image
counting with the actual mixed line. The intersection bound is explicit:
this module proves the subsequent action transfer and does not assert the
still-needed bound or the final odd-layer residual containment.

Source: Stellmacher (9.3), printed p.50/PDF p.40, the transvection sentence
in the final R₀,C₀ paragraph of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_three_final_core_action_displacement_le_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    let vectors := ((ZAt ctx.Γ ctx.criticalPath.a).map embedding).subgroupOf centralizer
    let line := (mixed.map embedding).subgroupOf centralizer
    Nat.card ((ZAt ctx.Γ ctx.criticalPath.a).map embedding ⊓
      (pCore 2 centralizer).map centralizer.subtype : Subgroup H) ≤ 4 →
    ∃ normal : line.Normal,
      letI := normal
      let core := pCore 2 centralizer
      let layer := frattini core ⊔ line.subgroupOf core
      IsElementaryAbelian 2 (core ⧸ layer) ∧
        ∃ action : centralizer →* MulAut (core ⧸ layer),
          (∀ actor : centralizer, ∀ vector : core,
            action actor (QuotientGroup.mk' layer vector) =
              QuotientGroup.mk' layer (MulAut.conjNormal actor vector)) ∧
          action.ker = core ∧
          Nat.card (commutatorAction (vectors.map action) (core ⧸ layer)) ≤ 2 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let vectors := ((ZAt ctx.Γ ctx.criticalPath.a).map embedding).subgroupOf centralizer
  let line := (mixed.map embedding).subgroupOf centralizer
  let core := pCore 2 centralizer
  change Nat.card ((ZAt ctx.Γ ctx.criticalPath.a).map embedding ⊓
    core.map centralizer.subtype : Subgroup H) ≤ 4 → _
  intro hsmall
  have hgeometry := nine_three_mixed_order_two_and_sylow ctx hb hlarge first second config rank
  obtain ⟨normal, hmodule, action, hformula, hkernel⟩ :=
    nine_three_final_core_frattini_mixed_action ctx hb hlarge first second config hgeometry
  let _ := normal
  let layer := frattini core ⊔ line.subgroupOf core
  refine ⟨normal, hmodule, action, hformula, hkernel, ?_⟩
  have hdata := nine_three_final_centralizer_center_core ctx hb hlarge first second config
  have hmixed : mixed.map embedding ≤ (ZAt ctx.Γ ctx.criticalPath.a).map embedding :=
    Subgroup.map_mono (nine_three_normalized_pair_centralizer
      ctx hb hlarge first second config).1
  have hline : line ≤ vectors ⊓ core :=
    le_inf (Subgroup.subgroupOf_mono centralizer hmixed) (hdata.2.trans inf_le_right)
  have hlineCard : Nat.card line = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hmixed.trans hdata.1)).toEquiv,
      Subgroup.card_map_of_injective ctx.embedding_injective]
    exact hgeometry.1
  have hintersection : Nat.card (vectors ⊓ core : Subgroup centralizer) ≤ 4 := by
    rw [← Subgroup.card_map_of_injective centralizer.subtype_injective,
      Subgroup.map_inf _ _ _ centralizer.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hdata.1]
    exact hsmall
  have hcommutator : ⁅core, vectors⁆ ≤ vectors ⊓ core := by
    apply (Subgroup.map_le_map_iff_of_injective centralizer.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _ centralizer.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hdata.1]
    exact (nine_three_final_core_intersection_normalizer_and_commutator
      ctx hb hlarge first second config hgeometry).2
  have hbound := core_quotient_displacement_card_mul_le_intersection
    core vectors line layer hline le_sup_right hcommutator action hformula
  rw [hlineCard] at hbound
  change Nat.card (commutatorAction (vectors.map action) (core ⧸ layer)) ≤ 2
  have heq : 2 * Nat.card (commutatorAction (vectors.map action) (core ⧸ layer)) ≤
      Nat.card (vectors ⊓ core : Subgroup centralizer) := hbound
  omega

end Stellmacher.SectionNine
