module

public import Stellmacher.Recognition.LargeTerminalCentralizerCore
public import Stellmacher.SectionTen.TenOneLargeSylowCard

/-!
# The full centralizer core when the ambient Sylow has order2048

In a retained large terminal context with ambient Sylow order2048, the
literal first residual is the full two-core of an ambient involution
centralizer. The involution generates the omega-center of that same Sylow.

The first Frobenius20 quotient gives the exact formula |S0|=4|Q_first|,
so the second local member has two-core of order512. The proved residual
of order512 lies inside the full centralizer core, which in turn lies
inside this local core. Equality follows from these finite containments.
All subgroup maps are the original generated-join inclusion; no equality
between the local member and the full centralizer is an assumption.

This establishes the core identification in one of the two possible large
Sylow cases, for the subsequent Parrott recognition hypotheses. Source:
Stellmacher (10.1)(19) and its Sylow bound; Parrott's original centralizer
hypotheses use a two-core of order512.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

private theorem second_core_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 2048) :
    Nat.card (twoCoreIn ctx.second) = 512 := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let T := (S0 : Subgroup G).subgroupOf K
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  let P := GAt ctx.terminal.Γ cp.firstStep
  let Q := QAt ctx.terminal.Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hT : Nat.card T = 2048 :=
    (Nat.card_congr (subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv).trans hS
  have hratio : Nat.card T = 4 * Nat.card Q :=
    ten_one_large_sylow_card tenCtx middle hpath ctx.noTransvections
  have hQ : Nat.card Q = 512 := by omega
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  let e : P ≃* ctx.second := (P.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hcard : Nat.card (pCore 2 ctx.second) = Nat.card (pCore 2 P) := by
    rw [← pCore_map_iso 2 e]
    exact card_map_of_injective e.injective
  have hQeq : Q = (pCore 2 P).map P.subtype :=
    ctx.terminal.Γ.twoCoreAt_def cp.firstStep
  calc
    Nat.card (twoCoreIn ctx.second) = Nat.card (pCore 2 ctx.second) :=
      card_map_of_injective ctx.second.subtype_injective
    _ = Nat.card (pCore 2 P) := hcard
    _ = Nat.card Q := by rw [hQeq]; exact (card_map_of_injective P.subtype_injective).symm
    _ = 512 := hQ

public theorem LargeTerminalContext.involution_centralizer_core_eq_of_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 2048) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual := by
  obtain ⟨z, hz, hgen, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hR : ctx.firstResidual = twoCoreIn ctx.second :=
    eq_of_le_of_card_ge (hlow.trans hhigh) (by
      rw [ctx.first_residual_structure.1, second_core_card ctx hS])
  exact ⟨z, hz, hgen, le_antisymm (hhigh.trans hR.ge) hlow⟩

end Stellmacher.Recognition
