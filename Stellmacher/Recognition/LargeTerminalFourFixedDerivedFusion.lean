module

public import Stellmacher.Recognition.LargeTerminalFiveFixedInvolution
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalFiveFixedOuterTransport
public import Stellmacher.Recognition.LargeTerminalOuterCosetDerivedFusion

/-!
# Assembling fusion into the derived residual

The outer-coset census fuses involutions of Q outside C_Q(D) into D.
Transporting an actual five-fixed involution into that region then gives
its fusion into D by transitivity. The final theorem combines the proved
outer-coset fusion and transport under the original five-fixed hypotheses.

Source: Thompson VI, printed p.630, the coset census and transport through
C_G(Z*). No ambient Sylow-five status is used in this assembly.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- Fusion into the derived residual follows by transporting to the region
covered by the outer-coset census. The two geometric inputs are explicit. -/
public theorem LargeTerminalContext.five_fixed_derived_fusion_of_transport
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (houter : ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) → orderOf x = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj x t)
    (htransport : ∀ y : G, y ∈ twoCoreIn ctx.second →
      y ∈ centralizer (A : Set G) → y ∉ ctx.firstResidual → orderOf y = 2 →
      ∃ x : G, x ∈ twoCoreIn ctx.second ∧
        x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ IsConj y x) :
    ∀ y : G, y ∈ twoCoreIn ctx.second → y ∈ centralizer (A : Set G) →
      y ∉ ctx.firstResidual → orderOf y = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj y t := by
  intro y hyQ hyA hyR hy
  obtain ⟨x, hxQ, hxC, hyx⟩ := htransport y hyQ hyA hyR hy
  have hx : orderOf x = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hyx
    exact ((MulAut.conj g).orderOf_eq y).trans hy
  obtain ⟨t, htD, hxt⟩ := houter x hxQ hxC hx
  exact ⟨t, htD, hyx.trans hxt⟩

/-- Every actual five-fixed involution outside the first residual is
conjugate into its derived subgroup. Transport puts it outside the derived
centralizer in the second core, where the outer-coset fusion applies. -/
public theorem LargeTerminalContext.five_fixed_derived_fusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second))) :
    ∀ y : G, y ∈ twoCoreIn ctx.second → y ∈ centralizer (A : Set G) →
      y ∉ ctx.firstResidual → orderOf y = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj y t := by
  exact ctx.five_fixed_derived_fusion_of_transport A
    (ctx.outer_coset_derived_fusion hS A hA hAN hcard hfixed hncyc)
    (ctx.five_fixed_outer_transport hS A hA hAN hfixed)

end Stellmacher.Recognition
