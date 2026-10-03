module

public import Stellmacher.SectionNine.NineThreeFinalCentralizerSetup
public import Stellmacher.SectionNine.NineThreeRankData

/-!
# The remaining order-eight case for the final core intersection in (9.3)

The actual initial center has order sixteen, and its image is not contained
in the actual final centralizer's two-core. Lagrange's theorem therefore
reduces failure of the requested order-four bound to intersection order eight.
This is only a reduction: the rank-two odd-layer action must still exclude
that order-eight case. Source: printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_three_final_core_intersection_card_eq_eight_of_gt_four
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
    let core := (pCore 2 centralizer).map centralizer.subtype
    4 < Nat.card ((ZAt ctx.Γ ctx.criticalPath.a).map embedding ⊓ core : Subgroup H) →
      Nat.card ((ZAt ctx.Γ ctx.criticalPath.a).map embedding ⊓ core : Subgroup H) = 8 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let core := (pCore 2 centralizer).map centralizer.subtype
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  have hcard : Nat.card vectors = 16 := by
    rw [← Nat.card_congr ((ZAt ctx.Γ ctx.criticalPath.a).equivMapOfInjective
      embedding ctx.embedding_injective).toEquiv]
    exact rank.center_card
  have hdivides : Nat.card (vectors ⊓ core : Subgroup H) ∣ 16 :=
    hcard ▸ Subgroup.card_dvd_of_le (show vectors ⊓ core ≤ vectors from inf_le_left)
  have hnot : Nat.card (vectors ⊓ core : Subgroup H) ≠ 16 := by
    intro heq
    have hsame : vectors ⊓ core = vectors :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact nine_three_initial_center_not_le_final_centralizer_core
      ctx hb hlarge first second config (hsame.ge.trans inf_le_right)
  have hdivisors : ∀ number : ℕ, number ∣ 16 →
      number = 1 ∨ number = 2 ∨ number = 4 ∨ number = 8 ∨ number = 16 := by
    intro number hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < 16) hdiv
    interval_cases number <;> norm_num at *
  have hcases := hdivisors _ hdivides
  change 4 < Nat.card (vectors ⊓ core : Subgroup H) →
    Nat.card (vectors ⊓ core : Subgroup H) = 8
  intro hgt
  omega

end Stellmacher.SectionNine
