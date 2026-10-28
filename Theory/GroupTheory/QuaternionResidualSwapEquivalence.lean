module
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Defs
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Theory.GroupTheory.CentralProductEquivalence
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Comparing residual central products with a swapping involution

Two residual central products of actual SL₂(3) factors have a canonical
comparison once one factor map and the two exchanging involutions are chosen.
The common centers have order two, so the transported factor maps agree on
the overlap. Central-product gluing gives an equivariant residual equivalence;
the complementary involutions then extend it to the whole groups.

The final transport lemmas retain the intrinsic two-core, its embedded center,
and the subgroup C_{O₂(G)}(v)⟨v⟩. The source consumer is the ordinary point
endpoint in Aschbacher--Smith 13.5.17, printed p.922; the residual factors
come from 14.2.21, printed p.988. No whole-group equivalence is assumed.
-/

public section
open Subgroup
namespace Subgroup
private theorem overlap_center {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a*b=b*a)
    (hi : Nat.card (A ⊓ B : Subgroup G)=2) (hz : Nat.card (center A)=2) :
    (center A).map A.subtype = A ⊓ B := by
  symm
  apply eq_of_le_of_card_ge
  · intro x hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact hc a a.property x hx.2
  · rw [card_map_of_injective A.subtype_injective,hz,hi]

private theorem overlap_compat_forward {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (A B : Subgroup G) (A' B' : Subgroup H)
    (hA : (center A).map A.subtype=A⊓B)
    (hB : (center B).map B.subtype=A⊓B)
    (hA' : (center A').map A'.subtype=A'⊓B')
    (hB' : (center B').map B'.subtype=A'⊓B')
    (hi' : Nat.card (A'⊓B' : Subgroup H)=2)
    (eA : A ≃* A') (eB : B ≃* B') (a : A) (b : B)
    (he : (a:G)=(b:G)) : (eA a:H)=(eB b:H) := by
  have ha : a∈center A := by
    have hh : (a:G)∈(center A).map A.subtype := hA ▸ ⟨a.property,he ▸ b.property⟩
    obtain ⟨x,hx,hxa⟩ := hh
    exact (Subtype.ext hxa : x=a) ▸ hx
  have hb : b∈center B := by
    have hh : (b:G)∈(center B).map B.subtype := hB ▸ ⟨he ▸ a.property,b.property⟩
    obtain ⟨x,hx,hxb⟩ := hh
    exact (Subtype.ext hxb : x=b) ▸ hx
  have ha' : (eA a:H)∈A'⊓B' := hA' ▸ mem_map_of_mem A'.subtype
    ((centerCongr eA ⟨a,ha⟩).property)
  have hb' : (eB b:H)∈A'⊓B' := hB' ▸ mem_map_of_mem B'.subtype
    ((centerCongr eB ⟨b,hb⟩).property)
  by_cases ha1 : a=1
  · have hb1 : b=1 := Subtype.ext (by rw [←he,ha1]; rfl)
    simp [ha1,hb1]
  · have hb1 : b≠1 := fun h => ha1 (Subtype.ext (by rw [he,h]; rfl))
    obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : (A'⊓B' : Subgroup H))).mp hi'
    have hnA : (⟨eA a,ha'⟩ : (A'⊓B' : Subgroup H))≠1 := by
      intro h
      apply ha1
      apply eA.injective
      apply Subtype.ext
      exact (congrArg Subtype.val h).trans (by simp)
    have hnB : (⟨eB b,hb'⟩ : (A'⊓B' : Subgroup H))≠1 := by
      intro h
      apply hb1
      apply eB.injective
      apply Subtype.ext
      exact (congrArg Subtype.val h).trans (by simp)
    exact congrArg Subtype.val ((hz _ hnA).trans (hz _ hnB).symm)

private theorem exists_equivariant_central_product
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (A B : Subgroup G) (A' B' : Subgroup H)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a*b=b*a)
    (hc' : ∀ a ∈ A', ∀ b ∈ B', a*b=b*a)
    (hg : A⊔B=⊤) (hg' : A'⊔B'=⊤)
    (hi : Nat.card (A⊓B : Subgroup G)=2) (hi' : Nat.card (A'⊓B' : Subgroup H)=2)
    (hzA : Nat.card (center A)=2) (hzB : Nat.card (center B)=2)
    (hzA' : Nat.card (center A')=2) (hzB' : Nat.card (center B')=2)
    (s : MulAut G) (t : MulAut H) (hs2 : Function.Involutive s)
    (ht2 : Function.Involutive t)
    (hs : A.map s.toMonoidHom=B) (ht : A'.map t.toMonoidHom=B')
    (eA : A ≃* A') :
    ∃ e : G ≃* H, (∀ a : A, e a=(eA a:H)) ∧ ∀ x, e (s x)=t (e x) := by
  let u : A ≃* B := (s.subgroupMap A).trans (MulEquiv.subgroupCongr hs)
  let w : A' ≃* B' := (t.subgroupMap A').trans (MulEquiv.subgroupCongr ht)
  let eB : B ≃* B' := u.symm.trans (eA.trans w)
  have hA := overlap_center A B hc hi hzA
  have hB : (center B).map B.subtype=A⊓B := by
    simpa only [inf_comm] using overlap_center B A (fun b hb a ha => (hc a ha b hb).symm)
      (by simpa only [inf_comm] using hi) hzB
  have hA' := overlap_center A' B' hc' hi' hzA'
  have hB' : (center B').map B'.subtype=A'⊓B' := by
    simpa only [inf_comm] using overlap_center B' A' (fun b hb a ha => (hc' a ha b hb).symm)
      (by simpa only [inf_comm] using hi') hzB'
  obtain ⟨e,heA,heB⟩ := exists_mulEquiv_of_central_products A B A' B'
    (fun a b => hc a a.property b b.property) (fun a b => hc' a a.property b b.property)
    hg hg' eA eB (fun a b => ⟨
      overlap_compat_forward A B A' B' hA hB hA' hB' hi' eA eB a b,
      fun h => by simpa only [MulEquiv.symm_apply_apply] using
        overlap_compat_forward A' B' A B hA' hB' hA hB hi eA.symm eB.symm (eA a) (eB b) h⟩)
  refine ⟨e,heA,?_⟩
  let F := (e.toMonoidHom.comp s.toMonoidHom).eqLocus (t.toMonoidHom.comp e.toMonoidHom)
  have hleft : A≤F := by
    intro a ha
    change e (s a)=t (e a)
    rw [heA ⟨a,ha⟩]
    have hh := heB (u ⟨a,ha⟩)
    change e (s a) = (w (eA (u.symm (u ⟨a,ha⟩))):H) at hh
    rw [MulEquiv.symm_apply_apply] at hh
    exact hh
  have hright : B≤F := by
    intro b hb
    obtain ⟨a,ha⟩ := u.surjective ⟨b,hb⟩
    have hab : s (a:G)=b := congrArg Subtype.val ha
    change e (s b)=t (e b)
    rw [←hab,hs2]
    have hlefta : e (s (a:G))=t (e (a:G)) := hleft a.property
    rw [hlefta,ht2]
  have hall : ⊤≤F := hg ▸ sup_le hleft hright
  exact fun x => hall (mem_top x)

private theorem restrict_swap {G : Type*} [Group G] (R A B : Subgroup G)
    [R.Normal] (hA : A≤R) (hB : B≤R) (v : G)
    (hs : A.map (MulAut.conj v).toMonoidHom=B) :
    (A.subgroupOf R).map (MulAut.conjNormal v : MulAut R).toMonoidHom=B.subgroupOf R := by
  apply map_injective R.subtype_injective
  rw [map_map]
  have hf : R.subtype.comp (MulAut.conjNormal v : MulAut R).toMonoidHom =
      (MulAut.conj v).toMonoidHom.comp R.subtype := by ext x; rfl
  rw [hf,←map_map,map_subgroupOf_eq_of_le hA,hs,map_subgroupOf_eq_of_le hB]

private theorem conj_involutive {G : Type*} [Group G] (v : G) (hv : v^2=1) :
    Function.Involutive (MulAut.conj v) := by
  intro x
  have hh : (MulAut.conj v)^2=1 := by rw [←map_pow,hv,map_one]
  exact congrArg (fun a : MulAut G => a x) hh

private theorem sl23_center_card_of_equiv {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (center J)=2 := (Nat.card_congr (centerCongr e).toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_center_card

private theorem exists_residual_equiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {Q : Subgroup G} {Q' : Subgroup H}
    {d : QuaternionCentralProductData Q} {d' : QuaternionCentralProductData Q'}
    (c : QuaternionResidualCentralProduct Q d) (c' : QuaternionResidualCentralProduct Q' d')
    (v : G) (w : H) (hv : v^2=1) (hw : w^2=1)
    (hs : c.left.map (MulAut.conj v).toMonoidHom=c.right)
    (ht : c'.left.map (MulAut.conj w).toMonoidHom=c'.right)
    (eL : c.left ≃* c'.left) :
    ∃ e : pResidual 2 G ≃* pResidual 2 H,
      (∀ a : c.left, (e ⟨a,(show c.left≤pResidual 2 G from le_sup_left.trans c.span.le) a.property⟩:H)=(eL a:H)) ∧
      ∀ x, e ((MulAut.conjNormal v : MulAut (pResidual 2 G)) x)=
        (MulAut.conjNormal w : MulAut (pResidual 2 H)) (e x) := by
  let R := pResidual 2 G
  let R' := pResidual 2 H
  have hL : c.left≤R := le_sup_left.trans c.span.le
  have hB : c.right≤R := le_sup_right.trans c.span.le
  have hL' : c'.left≤R' := le_sup_left.trans c'.span.le
  have hB' : c'.right≤R' := le_sup_right.trans c'.span.le
  let A := c.left.subgroupOf R
  let B := c.right.subgroupOf R
  let A' := c'.left.subgroupOf R'
  let B' := c'.right.subgroupOf R'
  let eA := (subgroupOfEquivOfLe hL).trans (eL.trans (subgroupOfEquivOfLe hL').symm)
  have hgen : A⊔B=⊤ := by rw [←subgroupOf_sup hL hB,c.span,subgroupOf_self]
  have hgen' : A'⊔B'=⊤ := by rw [←subgroupOf_sup hL' hB',c'.span,subgroupOf_self]
  have hi : Nat.card (A⊓B : Subgroup R)=2 := by
    change Nat.card ((c.left⊓c.right).subgroupOf R)=2
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hL)).toEquiv,
      c.intersection,card_map_of_injective Q.subtype_injective,d.center_card]
  have hi' : Nat.card (A'⊓B' : Subgroup R')=2 := by
    change Nat.card ((c'.left⊓c'.right).subgroupOf R')=2
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hL')).toEquiv,
      c'.intersection,card_map_of_injective Q'.subtype_injective,d'.center_card]
  obtain ⟨e,he,ha⟩ := exists_equivariant_central_product A B A' B'
    (fun a ha b hb => Subtype.ext (c.commute a ha b hb))
    (fun a ha b hb => Subtype.ext (c'.commute a ha b hb)) hgen hgen' hi hi'
    (sl23_center_card_of_equiv ((subgroupOfEquivOfLe hL).trans c.left_model.some))
    (sl23_center_card_of_equiv ((subgroupOfEquivOfLe hB).trans c.right_model.some))
    (sl23_center_card_of_equiv ((subgroupOfEquivOfLe hL').trans c'.left_model.some))
    (sl23_center_card_of_equiv ((subgroupOfEquivOfLe hB').trans c'.right_model.some))
    (MulAut.conjNormal v) (MulAut.conjNormal w)
    (fun x => Subtype.ext (conj_involutive v hv x))
    (fun x => Subtype.ext (conj_involutive w hw x))
    (restrict_swap R c.left c.right hL hB v hs)
    (restrict_swap R' c'.left c'.right hL' hB' w ht) eA
  exact ⟨e,fun a => congrArg Subtype.val (he ⟨⟨a,hL a.property⟩,a.property⟩),ha⟩

private theorem cyclic_generator {G : Type*} [Group G] (v : G) :
    ∀ x : zpowers v, x∈zpowers (⟨v,mem_zpowers v⟩ : zpowers v) := by
  intro x
  obtain ⟨n,hn⟩ := x.property
  exact mem_zpowers_iff.mpr ⟨n,Subtype.ext hn⟩

private theorem exists_equiv_of_involution_complements
    {G H : Type*} [Group G] [Group H]
    (R : Subgroup G) (S : Subgroup H) [R.Normal] [S.Normal]
    (v : G) (w : H) (hv : orderOf v=2) (hw : orderOf w=2)
    (hcomp : R.IsComplement' (zpowers v)) (hcomp' : S.IsComplement' (zpowers w))
    (eR : R ≃* S)
    (ha : ∀ x, eR ((MulAut.conjNormal v : MulAut R) x)=
        (MulAut.conjNormal w : MulAut S) (eR x)) :
    ∃ e : G ≃* H, e v=w ∧ ∀ x : R, e x=(eR x:H) := by
  let vg : zpowers v := ⟨v,mem_zpowers v⟩
  let wg : zpowers w := ⟨w,mem_zpowers w⟩
  have horder : orderOf vg=orderOf wg := by rw [←orderOf_coe vg,←orderOf_coe wg]; exact hv.trans hw.symm
  let eC := mulEquivOfOrderOfEq (cyclic_generator v) (cyclic_generator w) horder
  have heC : eC vg=wg := mulEquivOfOrderOfEq_apply_gen _ _ _
  have hvg : vg≠1 := by
    intro h
    have hh := congrArg Subtype.val h
    change v=1 at hh
    have := hv
    rw [hh,orderOf_one] at this
    contradiction
  have hc : Nat.card (zpowers v)=2 := (Nat.card_zpowers v).trans hv
  have cases (x : zpowers v) : x=1 ∨ x=vg := by
    by_cases h : x=1
    · exact Or.inl h
    · obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : zpowers v)).mp hc
      exact Or.inr ((hz x h).trans (hz vg hvg).symm)
  let f := SemidirectProduct.mulEquivSubgroup hcomp
  let g := SemidirectProduct.mulEquivSubgroup hcomp'
  have hact (x : zpowers v) :
      (((R.normalizerMonoidHom).comp (inclusion (R.normalizer_eq_top ▸ le_top))) x).trans eR =
      eR.trans ((((S.normalizerMonoidHom).comp
        (inclusion (S.normalizer_eq_top ▸ le_top))) (eC x))) := by
    rcases cases x with rfl | rfl
    · ext r
      simp
    · rw [heC]
      ext r
      exact congrArg Subtype.val (ha r)
  let eS := SemidirectProduct.congr eR eC hact
  let e := f.symm.trans (eS.trans g)
  have hR (x : R) : e x=(eR x:H) := by
    have hh : f (SemidirectProduct.inl x)=(x:G) := by simp [f]
    rw [←hh]
    change g (eS (f.symm (f _)))= _
    rw [f.symm_apply_apply]
    simp [eS,g]
  refine ⟨e,?_,hR⟩
  have hh : f (SemidirectProduct.inr vg)=v := by simp [f,vg]
  rw [←hh]
  change g (eS (f.symm (f _)))= _
  rw [f.symm_apply_apply]
  simpa [eS,g,wg] using congrArg (fun x : zpowers w => (x:H)) heC

namespace QuaternionResidualCentralProduct

/-- The factor comparison already identifies the residuals equivariantly, even
when the swapping involution generates only a proper subgroup of the ambient
group. This is the normal ordinary subgroup used in the doubled point case. -/
theorem exists_residual_equiv_of_swap
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {Q : Subgroup G} {Q' : Subgroup H}
    {d : QuaternionCentralProductData Q} {d' : QuaternionCentralProductData Q'}
    (c : QuaternionResidualCentralProduct Q d) (c' : QuaternionResidualCentralProduct Q' d')
    (v : G) (w : H) (hv : v^2=1) (hw : w^2=1)
    (hs : c.left.map (MulAut.conj v).toMonoidHom=c.right)
    (ht : c'.left.map (MulAut.conj w).toMonoidHom=c'.right)
    (eL : c.left ≃* c'.left) :
    ∃ e : pResidual 2 G ≃* pResidual 2 H,
      (∀ a : c.left, (e ⟨a,(show c.left≤pResidual 2 G from
        le_sup_left.trans c.span.le) a.property⟩:H)=(eL a:H)) ∧
      ∀ x, e ((MulAut.conjNormal v : MulAut (pResidual 2 G)) x)=
        (MulAut.conjNormal w : MulAut (pResidual 2 H)) (e x) :=
  exists_residual_equiv c c' v w hv hw hs ht eL

/-- An actor exchanging the distinct residual factors is a nontrivial involution. -/
theorem swapper_order_two {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} {d : QuaternionCentralProductData Q}
    (c : QuaternionResidualCentralProduct Q d) (v : G) (hv : v^2=1)
    (hs : c.left.map (MulAut.conj v).toMonoidHom=c.right) : orderOf v=2 := by
  apply orderOf_eq_prime hv
  intro h
  have he : c.left=c.right := by
    have hf : (MulAut.conj v).toMonoidHom=MonoidHom.id G := by subst v; ext x; simp
    simpa only [hf,map_id] using hs
  have hi : Nat.card (c.left⊓c.right : Subgroup G)=2 := by
    rw [c.intersection,card_map_of_injective Q.subtype_injective,d.center_card]
  have hl : Nat.card c.left=24 := (Nat.card_congr c.left_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  rw [←he,inf_idem,hl] at hi
  contradiction

/-- A chosen left-factor map extends over the central product and its
swapping involution. The right-factor map is forced by the two swaps. -/
theorem exists_mulEquiv_of_swap
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {Q : Subgroup G} {Q' : Subgroup H}
    {d : QuaternionCentralProductData Q} {d' : QuaternionCentralProductData Q'}
    (c : QuaternionResidualCentralProduct Q d) (c' : QuaternionResidualCentralProduct Q' d')
    (v : G) (w : H) (hv : v^2=1) (hw : w^2=1)
    (hcomp : (pResidual 2 G).IsComplement' (zpowers v))
    (hcomp' : (pResidual 2 H).IsComplement' (zpowers w))
    (hs : c.left.map (MulAut.conj v).toMonoidHom=c.right)
    (ht : c'.left.map (MulAut.conj w).toMonoidHom=c'.right)
    (eL : c.left ≃* c'.left) :
    ∃ e : G ≃* H, e v=w ∧ ∀ a : c.left, e a=(eL a:H) := by
  obtain ⟨eR,heR,ha⟩ := exists_residual_equiv c c' v w hv hw hs ht eL
  obtain ⟨e,he,hr⟩ := exists_equiv_of_involution_complements (pResidual 2 G) (pResidual 2 H)
    v w (c.swapper_order_two v hv hs) (c'.swapper_order_two w hw ht) hcomp hcomp' eR ha
  refine ⟨e,he,fun a => ?_⟩
  exact (hr ⟨a,(show c.left≤pResidual 2 G from le_sup_left.trans c.span.le) a.property⟩).trans (heR a)
end QuaternionResidualCentralProduct

/-- The marked elementary subgroup obtained from a swap and the intrinsic
core is preserved by any equivalence retaining that swap. -/
theorem map_fixed_core_join_zpowers {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (v : G) :
    ((pCore 2 G ⊓ centralizer ({v} : Set G)) ⊔ zpowers v).map e.toMonoidHom =
      (pCore 2 H ⊓ centralizer ({e v} : Set H)) ⊔ zpowers (e v) := by
  rw [map_sup,map_inf _ _ _ e.injective,pCore_map_iso,
    Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton,MonoidHom.map_zpowers]
  rfl

/-- The embedded center of the two-core is intrinsic under recognition. -/
theorem map_center_two_core {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    ((center (pCore 2 G)).map (pCore 2 G).subtype).map e.toMonoidHom =
      (center (pCore 2 H)).map (pCore 2 H).subtype := by
  rw [map_map,←map_center_image_of_injective _ _ e.injective,pCore_map_iso]
end Subgroup
