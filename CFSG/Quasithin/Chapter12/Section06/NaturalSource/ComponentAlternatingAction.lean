module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRanks
public import Theory.SpecificGroups.Alternating.SevenEightInvolutionOrders
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Alternating.Aut

/-!
# Faithful cubic planes exclude the A₇ and A₈ component quotients

The action of the original KL₁V on K-star descends faithfully through
its center, since K-star is perfect. A marking of the central quotient
as A₇ or A₈ therefore gives a literal permutation action. The original
Sylow E₉ would inject into the centralizer of the marked V-involution.
For A₇ its order is not divisible by nine. For A₈, the embedded component
and the original Sylow-centrality also force a factor of 64 in that same
centralizer, contradicting the cycle-type order calculation.

The constructor in ComponentAlternating supplies every hypothesis from
the original source configuration. No assertion about the full cubic
A₇ cover is made when its E₉ action has a kernel.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
variable {G : Type*} [Group G] [Finite G] {E : Setup G} {H : Subgroup G}
  {c : E.SelectedComponent H} (a : c.ActionMarking)

/-- The actual Sylow E₉ cannot act faithfully in the A₇ or A₈ quotient row. -/
theorem not_faithful_alternating_sylow {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : (star H c.K ⧸ center (star H c.K)) ≃* alternatingGroup (Fin n))
    (P : Sylow 3 E.L₁) (hP : Nat.card P = 9)
    (hcentral : let U := ((E.V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
        U ≤ centralizer (R : Set a.action.range)) :
    ¬ Function.Injective (a.residualSylowAction P) := by
  intro hi
  let B := star H c.K
  let := c.component.2
  let permAut : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
      (by rcases hn with rfl|rfl <;> decide) (by rcases hn with rfl|rfl <;> decide))
  let f : MulAut B →* Equiv.Perm (Fin n) :=
    permAut.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)
  have hf : Function.Injective f := permAut.symm.injective.comp
    (MulAut.centralQuotientAction_injective e)
  let U := (E.V.subgroupOf c.localActor).map a.action
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [a.module_card])
  have hto : orderOf (f (t : MulAut B)) = 2 :=
    (orderOf_injective f hf t).trans
      ((orderOf_injective U.subtype U.subtype_injective t).trans ht)
  let C := centralizer ({f t} : Set (Equiv.Perm (Fin n)))
  let g₀ := f.comp (a.residualSylowAction P)
  have hgmem (p : P) : g₀ p ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have hAX : E.L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
    have hm : a.residualSylowAction P p ∈ (E.L₁.subgroupOf c.localActor).map a.action :=
      ⟨⟨p.val.val,hAX p.val.property⟩,p.val.property,rfl⟩
    have he := (a.residual_centralizes hm t t.property).symm
    change f (a.residualSylowAction P p) * f t = f t * f (a.residualSylowAction P p)
    simpa only [map_mul] using congrArg f he
  let g := g₀.codRestrict C hgmem
  have hg : Function.Injective g := by
    intro x y he
    exact hi (hf (congrArg Subtype.val he))
  have h9 : 9 ∣ Nat.card C := hP ▸ card_dvd_of_injective g hg
  rcases hn with rfl|rfl
  · exact alternatingGroup.seven_not_nine_dvd_involution_centralizer _ hto h9
  · obtain ⟨R,_,hRC⟩ := hcentral
    have hKrange : (c.K.subgroupOf c.localActor).map a.action ≤ a.action.range := map_le_range _ _
    let k := (inclusion hKrange).comp a.componentQuotientEquiv.toMonoidHom
    have hk : Function.Injective k := (inclusion_injective hKrange).comp a.componentQuotientEquiv.injective
    have h64B : 2 ^ 6 ∣ Nat.card (B ⧸ center B) := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have h64R : 64 ∣ Nat.card R :=
      R.pow_dvd_card_of_pow_dvd_card (h64B.trans (card_dvd_of_injective k hk))
    let j₀ : R →* Equiv.Perm (Fin 8) := f.comp (a.action.range.subtype.comp (R : Subgroup a.action.range).subtype)
    have hjmem (r : R) : j₀ r ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      let t₀ : a.action.range := ⟨t, (map_le_range _ _ t.property)⟩
      have he := hRC (show t₀ ∈ U.subgroupOf a.action.range from t.property) r r.property
      change f (r.val.val) * f t = f t * f (r.val.val)
      simpa only [Subgroup.coe_mul,map_mul] using
        congrArg (fun x : a.action.range => f x.val) he
    let j := j₀.codRestrict C hjmem
    have hj : Function.Injective j := by
      intro x y he
      exact Subtype.ext (Subtype.ext (hf (congrArg Subtype.val he)))
    exact alternatingGroup.eight_not_nine_and_sixtyFour_dvd_involution_centralizer
      _ hto h9 (h64R.trans (card_dvd_of_injective j hj))

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
