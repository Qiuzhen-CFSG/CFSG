module

public import Stellmacher.Recognition.LargeTerminalCentralizerCore
public import Stellmacher.SectionTen.TenOneLargeSylowBounds

/-!
# Sylow order and residual index in the large terminal branch

The prescribed Sylow has order 2048 times the index of the first residual
in the second local member's two-core. Thus the two possible Sylow orders
correspond exactly to residual indices one and two. In particular, excluding
4096 requires excluding the proper residual extension; the local cardinal
bounds alone do not do this.

The Frobenius quotient gives the factor four between the Sylow and the
second core. The actual residual has order 512 and lies in that core.
The index formula and the existing Sylow bounds give the assertions.
Source: Stellmacher (10.1)(18)--(20) and the final bound on printed p.65.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

/-- The exact Sylow order formula, transported to the original second member. -/
public theorem LargeTerminalContext.sylow_card_eq_four_mul_second_core
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 4 * Nat.card (twoCoreIn ctx.second) := by
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
  have hT : Nat.card T = Nat.card S0 :=
    Nat.card_congr (subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv
  have hratio : Nat.card T = 4 * Nat.card Q :=
    ten_one_large_sylow_card tenCtx middle hpath ctx.noTransvections
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  let e : P ≃* ctx.second := (P.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hcard : Nat.card (pCore 2 ctx.second) = Nat.card (pCore 2 P) := by
    rw [← pCore_map_iso 2 e]
    exact card_map_of_injective e.injective
  have hQeq : Q = (pCore 2 P).map P.subtype :=
    ctx.terminal.Γ.twoCoreAt_def cp.firstStep
  have hcore : Nat.card (twoCoreIn ctx.second) = Nat.card Q := by
    calc
      Nat.card (twoCoreIn ctx.second) = Nat.card (pCore 2 ctx.second) :=
        card_map_of_injective ctx.second.subtype_injective
      _ = Nat.card (pCore 2 P) := hcard
      _ = Nat.card Q := by
        rw [hQeq]
        exact (card_map_of_injective P.subtype_injective).symm
  rw [hT, ← hcore] at hratio
  exact hratio

/-- The proper residual extension is exactly the extra factor in the Sylow order. -/
public theorem LargeTerminalContext.sylow_card_eq_residual_index_mul
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = ctx.firstResidual.relIndex (twoCoreIn ctx.second) * 2048 := by
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hle := hlow.trans hhigh
  have hi := (ctx.firstResidual.subgroupOf (twoCoreIn ctx.second)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    ctx.first_residual_structure.1] at hi
  change ctx.firstResidual.relIndex (twoCoreIn ctx.second) * 512 =
    Nat.card (twoCoreIn ctx.second) at hi
  rw [ctx.sylow_card_eq_four_mul_second_core, ← hi]
  omega

/-- The lower Sylow endpoint is equivalent to equality with the actual residual. -/
public theorem LargeTerminalContext.sylow_card_eq_2048_iff
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 2048 ↔ twoCoreIn ctx.second = ctx.firstResidual := by
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hle := hlow.trans hhigh
  constructor
  · intro hS
    have hi : ctx.firstResidual.relIndex (twoCoreIn ctx.second) = 1 := by
      have h := ctx.sylow_card_eq_residual_index_mul
      omega
    exact le_antisymm (relIndex_eq_one.mp hi) hle
  · intro heq
    rw [ctx.sylow_card_eq_four_mul_second_core, heq, ctx.first_residual_structure.1]

/-- The upper endpoint is equivalent to residual index two in the local core. -/
public theorem LargeTerminalContext.sylow_card_eq_4096_iff
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 4096 ↔ ctx.firstResidual.relIndex (twoCoreIn ctx.second) = 2 := by
  have h := ctx.sylow_card_eq_residual_index_mul
  omega

/-- Both numerical endpoints remain possible in the purely local bounds. -/
public theorem LargeTerminalContext.sylow_card_cases
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 2048 ∨ Nat.card S0 = 4096 := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hcard : Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) =
      Nat.card S0 :=
    Nat.card_congr (subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv
  have hb := ten_one_large_sylow_card_bounds tenCtx middle hpath ctx.noTransvections
  change 2 ^ 11 ≤ Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) ∧
    Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) ≤ 2 ^ 12 at hb
  rw [hcard] at hb
  obtain ⟨n, hn⟩ := S0.isPGroup'.exists_card_eq
  rw [hn] at hb ⊢
  have hlo : 11 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb.1
  have hhi : n ≤ 12 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb.2
  have he : n = 11 ∨ n = 12 := by omega
  rcases he with rfl | rfl <;> norm_num

end Stellmacher.Recognition
