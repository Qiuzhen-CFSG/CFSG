module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalFiveFixedLineNormal
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Confinement of the actual five-centralizer

In the noncyclic four-fixed alternative, the distinguished order-two line
is normal in the five-centralizer. A normal subgroup of order two is central,
so the five-centralizer fixes the distinguished involution. The full
involution-centralizer theorem identifies its centralizer with the second
local subgroup, proving the requested confinement.

The saved reductions remain available: residual fixed points equal the
residual center, and line normality together with the full quotient bound
suffices for confinement. The unconditional theorem discharges these inputs
using the fixed-four and involution-centralizer developments.

Source: Thompson VI, printed p.630, the five-normalizer assertion in the
noncyclic four-fixed alternative. No odd-local solvability or ambient
Sylow-five hypothesis is needed.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- Every residual-normalizing actor centralizes the distinguished line. -/
public theorem LargeTerminalContext.omegaOneCenter_le_five_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G)) :
    omegaOneCenter (S : Subgroup G) ≤ centralizer (A : Set G) := by
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  have hAC := ctx.five_le_involution_centralizer A hAN z hz hgen
  rw [← centralizer_closure, ← zpowers_eq_closure, hgen] at hAC
  exact le_centralizer_iff.mp hAC

/-- The supplied bound on residual fixed points is an equality, since the
residual center is the line centralized by every residual-normalizing actor. -/
public theorem LargeTerminalContext.five_fixed_residual_eq_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    (centralizer (A : Set G)).subgroupOf ctx.firstResidual =
      center ctx.firstResidual := by
  apply le_antisymm hfixed
  intro r hr
  apply ctx.omegaOneCenter_le_five_centralizer A hAN
  rw [← ctx.first_residual_center_eq_omegaOneCenter]
  exact mem_map_of_mem ctx.firstResidual.subtype hr

/-- Normality of the distinguished line in the five-centralizer is the
global input which makes its elements centralize the distinguished involution. -/
public theorem LargeTerminalContext.five_centralizer_le_involution_centralizer_of_line_normal
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hline : ((omegaOneCenter (S : Subgroup G)).subgroupOf
      (centralizer (A : Set G))).Normal)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    centralizer (A : Set G) ≤ centralizer ({z} : Set G) := by
  let C := centralizer (A : Set G)
  let Z := omegaOneCenter (S : Subgroup G)
  change zpowers z = Z at hgen
  have hZC : Z ≤ C := ctx.omegaOneCenter_le_five_centralizer A hAN
  have hcard : Nat.card (Z.subgroupOf C) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv, ← hgen,
      Nat.card_zpowers, hz]
  let _ : (Z.subgroupOf C).Normal := hline
  have hcentral := central_of_normal_card_two (Z.subgroupOf C) hcard
  have hzZ : z ∈ Z := hgen ▸ mem_zpowers z
  have hzcenter : (⟨z, hZC hzZ⟩ : C) ∈ center C := hcentral hzZ
  intro c hc
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg C.subtype (mem_center_iff.mp hzcenter ⟨c, hc⟩)

/-- Assembly for five-centralizer confinement. The two remaining inputs
are the local quotient bound and normality of the distinguished line in
the full five-centralizer; odd-local solvability and ambient Sylow-five
status are not hypotheses of this reduction. -/
public theorem LargeTerminalContext.five_centralizer_le_second_of_line_normal_of_quotient_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hline : ((omegaOneCenter (S : Subgroup G)).subgroupOf
      (centralizer (A : Set G))).Normal)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (hquot : Nat.card (centralizer ({z} : Set G) ⧸
      pCore 2 (centralizer ({z} : Set G))) ≤ 20) :
    centralizer (A : Set G) ≤ ctx.second :=
  (ctx.five_centralizer_le_involution_centralizer_of_line_normal A hAN hline z hz hgen).trans_eq
    (ctx.involution_centralizer_eq_second_of_quotient_card_le hS z hz hgen hquot)

/-- The actual five-centralizer lies in the second local subgroup in the
noncyclic four-fixed alternative at Sylow order 4096. -/
public theorem LargeTerminalContext.five_centralizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    centralizer (A : Set G) ≤ ctx.second := by
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  exact (ctx.five_centralizer_le_involution_centralizer_of_line_normal A hAN
    (ctx.five_fixed_line_normal hS A hA hAP hAN hcard hncyc hfixed) z hz hgen).trans_eq
      (ctx.involution_centralizer_eq_second hS z hz hgen)

end Stellmacher.Recognition
