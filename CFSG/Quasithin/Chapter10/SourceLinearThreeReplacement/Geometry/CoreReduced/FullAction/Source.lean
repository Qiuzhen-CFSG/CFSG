module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Recognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Assembly

/-!
# Full-action contradiction for the diagonal centralizer

The original exchanger puts a and b in the same G_z orbit. The local
moved-factor calculation and the natural section supply at least four roots at a.
Reducedness of the full action, not a subgroup restriction, enables corrected
G.3.1. Its blocks exclude the nonzero fixed vector a+b. This bypasses the
later 10.2.4 model list and requires no spanning assertion.

The local natural-module input remains explicit. The final theorem applies
this reduction to CoreReducedAt using its existing assembly. The source
10.2.11 assertion is not yet unconditional: MovedFactorFixedAt must be proved.
Source: Aschbacher--Smith 10.2.11(3), printed p.754.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
open Subgroup Theory.GroupTheory BinaryTransvectionGroups
open scoped IsMulCommutative
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}


theorem contradiction_of_moved_factor (c : Configuration s a b)
    (hc : centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2))
    (hr : IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))))
    (hker : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    False := by
  let : IsElementaryAbelian 2 (centralizerModule a b) := c.span_elementary_of_central_core hc
  let H := (action c).range
  let x := firstVector (a := a) (b := b)
  let y : Additive (centralizerModule a b) :=
    Additive.ofMul ⟨b,le_conjugateSpanBy _ _ (mem_sup_right (mem_zpowers b))⟩
  have hx : x ≠ 0 := fun hh => c.first_ne (congrArg (fun v => (v.toMul:G)) hh)
  have hroot : 2 < Nat.card (rootGroup H x) := by
    have hle := movedAction_le_roots c (c.moved_displacement_le_line hc hker)
    have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    have hfour := (movedAction_card_ge_four c hker).trans hbound
    change 4 ≤ Nat.card (rootGroup H x) at hfour
    omega
  have hH := root_hypotheses_of_card hx (action_twoCore c hr) hroot
  have hy : y ∈ MulAction.orbit H x := by
    let t : centralizer ({a*b} : Set G) := ⟨s.exchange,c.sylow_le s.exchange_mem⟩
    refine MulAction.mem_orbit_iff.mpr ⟨⟨action c t,⟨t,rfl⟩⟩,?_⟩
    exact Subtype.ext c.exchange_first
  have hzero := fixed_sum_eq_zero hH (action_twoCore c hr)
    (MulAction.mem_orbit_self x) hy (by
      rintro g ⟨t,rfl⟩
      apply Subtype.ext
      change (t:G)*(a*b)*(t:G)⁻¹ = a*b
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property))
  have hz : a*b=1 := congrArg (fun v : Additive (centralizerModule a b) => (v.toMul:G)) hzero
  have ho := c.order
  rw [hz,orderOf_one] at ho
  omega

theorem fullActionCentralization_of_moved_factor (hlocal : MovedFactorFixedAt T) :
    FullActionCentralizationAt T := by
  intro L D s a b c hseed hcentral _hlt hred
  by_contra hn
  exact contradiction_of_moved_factor c hcentral hred (hlocal L D s a b c hseed hcentral hn)

theorem coreReduced_of_moved_factor (hseed : SeedAnalysisAt T)
    (hlocal : MovedFactorFixedAt T) : Geometry.CoreReducedAt T :=
  coreReduced_of_source_inputs hseed (fullActionCentralization_of_moved_factor hlocal)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
