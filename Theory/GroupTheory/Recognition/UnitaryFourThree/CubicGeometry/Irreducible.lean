module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Order
public import Theory.GroupAction.FiveOnEightyOneIrreducible

/-!
# Irreducibility of the original cubic kernel

The faithful normalizer quotient has order360 and therefore an order-five
actor. Its action on the original group V of order81 is nontrivial. The
five-action orbit count makes every invariant subgroup of V trivial or full.
This supplies the needed source geometry without assuming an A6 module model.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p247.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)
theorem kernel_irreducible (R:Subgroup G) (hRV:R≤c.toSourceData.V)
    (hMR:normalizer (c.toSourceData.V:Set G)≤normalizer (R:Set G)) :
    R=⊥ ∨ R=c.toSourceData.V := by
  let :Fact (Nat.Prime 5):=⟨by decide⟩
  let V:=c.toSourceData.V
  let B:=NormalizerAction.Star V
  let M:=normalizer (V:Set G)
  let q:=NormalizerAction.quotient V
  obtain ⟨a,ha⟩:=exists_prime_orderOf_dvd_card' (G:=B) 5 (by rw[c.quotient_card];decide)
  let A:=zpowers a
  have hA:Nat.card A=5:=by rw[Nat.card_zpowers,ha]
  let f:A→*MulAut V:=(NormalizerAction.action V).comp A.subtype
  let :MulDistribMulAction A V:=MulDistribMulAction.compHom V f
  have hfixed:FixedPoints.subgroup A V≠⊤:=by
    intro hh
    have he:NormalizerAction.action V a=1:=by
      ext v
      have hv:v∈FixedPoints.subgroup A V:=hh ▸ mem_top v
      exact congrArg Subtype.val (hv ⟨a,mem_zpowers a⟩)
    have ha1:a=1:=(NormalizerAction.action_injective V) (he.trans (map_one _).symm)
    rw[ha1,orderOf_one] at ha
    omega
  have hfix:=Theory.GroupAction.fixed_eq_bot_of_five_action_card_eighty_one hA c.kernel_card hfixed
  let D:=R.subgroupOf V
  let :IsInvariant A V D:=by
    constructor
    intro b v
    obtain ⟨m,hm⟩:=QuotientGroup.mk'_surjective (NormalizerAction.C V) (b:B)
    change (v:G)∈R ↔ ((NormalizerAction.action V (b:B)) v:G)∈R
    change q m=(b:B) at hm
    rw[←hm,NormalizerAction.action_quotient]
    change (v:G)∈R ↔ (m:G)*(v:G)*(m:G)⁻¹∈R
    exact mem_normalizer_iff.mp (hMR m.property) v
  rcases Theory.GroupAction.invariant_eq_bot_or_top_of_five_actor_on_eighty_one hA c.kernel_card hfix D with hb|ht
  · left
    apply bot_unique
    intro x hx
    have hxd:(⟨x,hRV hx⟩:V)∈D:=hx
    exact congrArg Subtype.val (mem_bot.mp (hb.le hxd))
  · right
    apply le_antisymm hRV
    intro x hx
    exact ht.ge (mem_top (⟨x,hx⟩:V))

end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
