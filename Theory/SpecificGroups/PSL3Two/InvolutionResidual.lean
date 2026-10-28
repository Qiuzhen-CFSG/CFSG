module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.Decomposition
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Two-perfect subgroups centralizing an involution of PSL₃(2)

The highest-root centralizer over F₂ is its unitriangular subgroup: the
centralizing torus has trivial unit group. Involution conjugacy gives the
same two-group property for every involution centralizer. The actual outer
automorphism quotient is a two-group, so a two-perfect subgroup of any
faithful extension first lies in the component and then vanishes if it
centralizes such an involution.

This uses the residual property, not just nontriviality of an arbitrary
centralizing subgroup. No new order, simplicity or automorphism
classification is undertaken here.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed p.924, the exclusion of L₃(2) using the nontrivial Y-hat.
-/

@[expose] public section
open Subgroup
open Matrix.PSL3.EvenInnerCentralizers
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3Two.InvolutionResidual

theorem root_centralizer_two : IsPGroup 2 (centralizer (ZMod 2)) := by
  have hu : IsPGroup 2 (U (ZMod 2)) := IsPGroup.of_card (n := 3) (by
    rw [card_U]; norm_num)
  apply hu.of_surjective (unipotentInCentralizer (ZMod 2))
  intro g
  obtain ⟨a,u,he⟩ := centralizer_factorization (ZMod 2) g
  have ha : a = 1 := Subsingleton.elim _ _
  rw [ha, map_one, one_mul] at he
  exact ⟨u,he.symm⟩

theorem centralizer_two (t : Matrix.PSL3Two.PSL) (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.centralizer {t}) := by
  have hr : orderOf (root (ZMod 2)) = 2 :=
    orderOf_eq_prime (root_sq (ZMod 2)) (root_ne_one (ZMod 2))
  obtain ⟨g,hg⟩ := Matrix.PSL3Two.involutions_conjugate t (root (ZMod 2)) ht hr
  let e := MulAut.conj g
  let f : Subgroup.centralizer {t} →* centralizer (ZMod 2) :=
    (e.toMonoidHom.comp (Subgroup.centralizer {t}).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change e x * root (ZMod 2) = root (ZMod 2) * e x
      have hx := congrArg e (mem_centralizer_singleton_iff.mp x.property)
      simpa only [map_mul, show e t = root (ZMod 2) from hg] using hx)
  exact root_centralizer_two.of_injective f (fun a b hh =>
    Subtype.ext (e.injective (congrArg Subtype.val hh)))

theorem sl_centralizer_two (t : Matrix.PSL3Two.SL) (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.centralizer {t}) := by
  let e := Matrix.PSL3Two.equiv
  let f : Subgroup.centralizer {t} →* Subgroup.centralizer {e t} :=
    (e.toMonoidHom.comp (Subgroup.centralizer {t}).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change e x * e t = e t * e x
      simpa only [map_mul] using (congrArg e
        (mem_centralizer_singleton_iff.mp x.property)))
  exact (centralizer_two (e t) ((e.orderOf_eq t).trans ht)).of_injective f
    (fun a b hh => Subtype.ext (e.injective (congrArg Subtype.val hh)))

variable {E : Type*} [Group E]

theorem residual_centralizing_eq_bot (K : Subgroup E) [K.Normal]
    (e : K ≃* Matrix.PSL3Two.SL) (hK : Subgroup.centralizer (K : Set E) = ⊥)
    (v : K) (hv : orderOf v = 2) (Y : Subgroup E) (hY : IsPPerfect 2 Y)
    (hc : Y ≤ Subgroup.centralizer {(v : E)}) : Y = ⊥ := by
  have hout : IsPGroup 2 (MulAut.Outer K) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
  have hq : IsPGroup 2 (E ⧸ K) :=
    hout.of_injective (MulAut.outerAction K) (MulAut.outerAction_injective K hK)
  have hkill := hY.hom_eq_one_of_isPGroup hq ((QuotientGroup.mk' K).comp Y.subtype)
  have hYK : Y ≤ K := by
    intro y hy
    apply (QuotientGroup.eq_one_iff y).mp
    exact congrArg (fun f : Y →* E ⧸ K => f ⟨y,hy⟩) hkill
  let f : Y →* Subgroup.centralizer {e v} :=
    (e.toMonoidHom.comp (inclusion hYK)).codRestrict _ (by
      intro y
      apply mem_centralizer_singleton_iff.mpr
      have hy : (inclusion hYK y) * v = v * (inclusion hYK y) :=
        Subtype.ext (mem_centralizer_singleton_iff.mp (hc y.property))
      change e (inclusion hYK y) * e v = e v * e (inclusion hYK y)
      simpa only [map_mul] using congrArg e hy)
  have hf := hY.hom_eq_one_of_isPGroup
    (sl_centralizer_two (e v) ((e.orderOf_eq v).trans hv)) f
  apply le_bot_iff.mp
  intro y hy
  have he : e (inclusion hYK ⟨y,hy⟩) = 1 :=
    congrArg (fun a : Y →* Subgroup.centralizer {e v} => (a ⟨y,hy⟩).val) hf
  exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))

theorem fitting_residual_centralizing_eq_bot [Finite E]
    (e : Theory.GroupTheory.generalizedFitting E ≃* Matrix.PSL3Two.SL)
    (v : Theory.GroupTheory.generalizedFitting E) (hv : orderOf v = 2)
    (Y : Subgroup E) (hY : IsPPerfect 2 Y)
    (hc : Y ≤ Subgroup.centralizer {(v : E)}) : Y = ⊥ := by
  apply residual_centralizing_eq_bot _ e ?_ v hv Y hY hc
  apply le_bot_iff.mp
  intro x hx
  have hxK := Theory.GroupTheory.centralizer_generalizedFitting_le E hx
  have hz : (⟨x,hxK⟩ : Theory.GroupTheory.generalizedFitting E) ∈
      center (Theory.GroupTheory.generalizedFitting E) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  have hze := ((centerCongr e) ⟨_, hz⟩).property
  change e ⟨x,hxK⟩ ∈ center Matrix.PSL3Two.SL at hze
  have hz1 : e ⟨x,hxK⟩ = 1 := by
    simpa only [Matrix.PSL3Two.center_eq_bot, mem_bot] using hze
  exact congrArg Subtype.val (e.injective (hz1.trans e.map_one.symm))

/-- A marked normal component equal to F*(E) needs no separately assumed
self-centralization. Its model's trivial center discharges that premise. -/
theorem residual_centralizing_eq_bot_of_fitting [Finite E]
    (K : Subgroup E) (hK : K = Theory.GroupTheory.generalizedFitting E)
    (e : K ≃* Matrix.PSL3Two.SL) (v : K) (hv : orderOf v = 2)
    (Y : Subgroup E) (hY : IsPPerfect 2 Y)
    (hc : Y ≤ Subgroup.centralizer {(v : E)}) : Y = ⊥ := by
  subst K
  exact fitting_residual_centralizing_eq_bot e v hv Y hY hc

end Matrix.PSL3Two.InvolutionResidual
