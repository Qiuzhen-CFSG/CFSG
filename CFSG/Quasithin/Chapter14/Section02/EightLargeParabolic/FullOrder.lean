module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullShortCentralizer
public import Theory.GroupTheory.InvolutionClassOrderComparison.Local

/-!
# Thompson order comparison including the original cubic endpoints

All involutions in either full endpoint lie in its marked base. Therefore
its mixed-pair fibers agree with the native fibers, even in the cubic case.
The two ambient centralizer orders acquire the same factor, the literal
index of H in Mc. Thompson's formula gives the ambient order with that
factor retained. No extension marking or ambient equivalence is assumed.

Source: Aschbacher--Smith F.4.43 and 14.2.18--19, printed pp.296,987.
The original component application is TerminalSolvable/EightBorelFullOrder.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.EvenInvolutionGeometry
open InvolutionClassOrderComparison
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

private def centralizerInfEquiv (L : Subgroup G) (t : L) :
    (L ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ≃*
      centralizer ({t} : Set L) where
  toFun x := ⟨⟨x,x.property.1⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  invFun x := ⟨x.val.val,x.val.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem conjugate_order {X : Type*} [Group X] {v w : X}
    (hc : IsConj v w) : orderOf v = orderOf w := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp hc
  exact ((MulAut.conj g).orderOf_eq v).symm

omit [Finite G] in
private theorem fusion_at {E : Type*} [Group E] (L : Subgroup G)
    (f : L →* E) (hf : Function.Injective f) (x : G) (y : E)
    (hx : orderOf x = 2) (hy : orderOf y = 2)
    (h : ∀ a : L, orderOf (a : G) = 2 → (IsConj x a.val ↔ IsConj y (f a)))
    (a : L) : IsConj x a.val ↔ IsConj y (f a) := by
  constructor
  · intro ha
    exact (h a ((conjugate_order ha).symm.trans hx)).mp ha
  · intro ha
    apply (h a ?_).mpr ha
    rw [Subgroup.orderOf_coe,←orderOf_injective f hf]
    exact (conjugate_order ha).symm.trans hy

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- F.4.43 with the actual common endpoint index retained. -/
theorem source_card_eq_triality_mul_index (r : MarkedTriality T M Mc H) :
    Nat.card G = Nat.card (Carrier P) * H.relIndex Mc := by
  let L := secondParabolic T M Mc H
  let t := markedShortRoot r (1 : ExtensionField P)
  have ht : orderOf (t : G) = 2 := markedShortRoot_order r 1 one_ne_zero
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hz2 : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime _ hzne
    have hp := pow_card_eq_one' (x := z)
    rwa [plane_centralInvolutions_card T M hM.1.2 hcard e] at hp
  have hTP : (T : Subgroup G) ≤ L := le_sup_right.trans le_sup_left
  let zH : H := ⟨z,hH.1.1.2 (centralInvolutions_le_sylow T z.property)⟩
  let zL : L := ⟨z,hTP (centralInvolutions_le_sylow T z.property)⟩
  let f : H →* Carrier P := (parabolic P .arms).subtype.comp r.left.toMonoidHom
  let g : L →* Carrier P := (parabolic P .central).subtype.comp r.right.toMonoidHom
  have hf : Function.Injective f := (parabolic P .arms).subtype_injective.comp r.left.injective
  have hg : Function.Injective g := (parabolic P .central).subtype_injective.comp r.right.injective
  let ze := g zL
  let te := g t
  have hzmark : f zH = ze := marked_endpoint_value r ⟨zH.property,zL.property⟩
  have hze : orderOf ze = 2 := (orderOf_injective g hg zL).trans
    ((Subgroup.orderOf_coe zL).symm.trans hz2)
  have hte : orderOf te = 2 := (orderOf_injective g hg t).trans
    ((Subgroup.orderOf_coe t).symm.trans ht)
  have hCz : centralizer ({(z : G)} : Set G) = Mc :=
    (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r z.property hz1).symm
  have hCze : centralizer ({ze} : Set (Carrier P)) = parabolic P .arms := by
    rw [←hzmark,highestRoot_centralizer_eq_localFactor 1 Nat.zero_lt_one (f zH)
      (marked_core_center_mem r zH (by rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]; exact z.property))
      (fun hh => hz1 (congrArg Subtype.val (hf (hh.trans f.map_one.symm)))),
      parabolic_arms_eq_localFactor_at_two P rfl (by simp only [binaryParameters_q,pow_one])]
  let eZ : H ≃* centralizer ({ze} : Set (Carrier P)) :=
    r.left.trans (MulEquiv.subgroupCongr hCze.symm)
  have heZ (x : H) : (eZ x).val = f x := rfl
  have hCt := source_short_centralizer_le hG hempty hM hu hmany hcard e hH r 1 one_ne_zero
  let C := centralizer ({(t : G)} : Set G)
  let A := L ⊓ C
  let tA : A := ⟨t,t.property,mem_centralizer_singleton_iff.mpr rfl⟩
  let eT : A ≃* centralizer ({te} : Set (Carrier P)) :=
    (centralizerInfEquiv L t).trans ((markedShortCentralizerEquiv r 1 one_ne_zero).trans
      (MulEquiv.subgroupCongr (congrArg (fun u : Carrier P => centralizer ({u} : Set (Carrier P)))
        (markedShortRoot_image r 1).symm)))
  have heT (x : A) : (eT x).val = g ⟨x,x.property.1⟩ := rfl
  have hneq : ¬ IsConj (z : G) (t : G) :=
    source_short_not_conj_center hG hempty hM hu hmany hcard e hH r 1 one_ne_zero z.property hz1
  have hneqe : ¬ IsConj ze te := fun hc => hneq
    ((source_second_fusion_iff hG hempty hM hu hmany hcard e hH r zL t hz2 ht).mpr hc)
  have hfusionH (x : L) (hx : orderOf (x : G) = 2) (a : H) :
      IsConj (x : G) (a : G) ↔ IsConj (g x) (f a) := by
    apply fusion_at H f hf x (g x) hx
      ((orderOf_injective g hg x).trans ((Subgroup.orderOf_coe x).symm.trans hx)) _ a
    intro b hb
    have hh := source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r b x hb hx
    exact ⟨fun h => (hh.mp h.symm).symm,fun h => (hh.mpr h.symm).symm⟩
  have hfusionL (x : L) (hx : orderOf (x : G) = 2) (a : L) :
      IsConj (x : G) (a : G) ↔ IsConj (g x) (g a) :=
    fusion_at L g hg x (g x) hx
      ((orderOf_injective g hg x).trans ((Subgroup.orderOf_coe x).symm.trans hx))
      (fun b hb => source_second_fusion_iff hG hempty hM hu hmany hcard e hH r x b hx hb) a
  have hclasses := source_involution_classes hG hempty hM hu hmany hcard e hH r
    1 one_ne_zero z.property hz1
  have hclassesE : ∀ x : Carrier P, orderOf x = 2 → IsConj ze x ∨ IsConj te x := by
    intro x hx
    let S := unipotentSylow P rfl
    have hS := coe_unipotentSylow P rfl
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,hx,pow_one])
    obtain ⟨b,_,hb⟩ := UniqueFixedCoset.p_element_conjugate_into_sylow S
      (show (S : Subgroup (Carrier P)) ≤ ⊤ from le_top) (mem_top x) hp
    rw [hS] at hb
    obtain ⟨y,hy,hym⟩ := marked_sylow_lift r hH.1.1.2 _ hb
    let yL : L := ⟨y,hTP hy⟩
    have he : g yL = b*x*b⁻¹ := (marked_endpoint_value r ⟨y.property,yL.property⟩).symm.trans hym
    have hy2 : orderOf (yL : G) = 2 := by
      rw [Subgroup.orderOf_coe,←orderOf_injective g hg,he]
      exact ((MulAut.conj b).orderOf_eq x).trans hx
    have hxy : IsConj x (g yL) := isConj_iff.mpr ⟨b,he.symm⟩
    rcases hclasses yL hy2 with h | h
    · exact Or.inl (((hfusionL zL hz2 yL).mp h).trans hxy.symm)
    · exact Or.inr (((hfusionL t ht yL).mp h).trans hxy.symm)
  have hiv := source_endpoint_involutions hG hempty hM hu hmany hcard e hH r
  have hzcount := kappa_eq_of_localCentralizer H (z:G) (t:G) zH ze te ze
    hz2 ht hneq hze hte hneqe
    (fun x hx hx2 => hiv.1 x (hCz ▸ hx) hx2) eZ (by rw [heZ]; exact hzmark)
    (fun a => by rw [heZ]; exact hfusionH zL hz2 a)
    (fun a => by rw [heZ]; exact hfusionH t ht a)
  have htcount := kappa_eq_of_localCentralizer A (z:G) (t:G) tA ze te te
    hz2 ht hneq hze hte hneqe
    (fun x hx hx2 => ⟨hiv.2 x (hCt hx) hx2,hx⟩) eT rfl
    (fun a => by rw [heT]; exact hfusionL zL hz2 ⟨a,a.property.1⟩)
    (fun a => by rw [heT]; exact hfusionL t ht ⟨a,a.property.1⟩)
  have hzcard : Nat.card (centralizer ({(z:G)} : Set G)) =
      Nat.card (centralizer ({ze} : Set (Carrier P))) * H.relIndex Mc := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) H Mc bot_le
      (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    simp only [relIndex_bot_left] at hh
    rw [hCz,←Nat.card_congr eZ.toEquiv]
    exact hh.symm
  have htcard : Nat.card (centralizer ({(t:G)} : Set G)) =
      Nat.card (centralizer ({te} : Set (Carrier P))) * H.relIndex Mc := by
    have hi := (source_short_centralizer_index hG hempty hM hu hmany hcard e hH r
      1 one_ne_zero).trans (source_endpoint_indices hG hempty hM hu hmany hcard e hH r)
    rw [inf_eq_right.mpr hCt] at hi
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) A C bot_le inf_le_right
    simp only [relIndex_bot_left] at hh
    rw [hi] at hh
    rw [←Nat.card_congr eT.toEquiv]
    exact hh.symm
  have hcG := TwoInvolutionClassOrder.card_eq (z:G) (t:G) hz2 ht hneq hclasses
  have hcE := TwoInvolutionClassOrder.card_eq ze te hze hte hneqe hclassesE
  rw [hzcount,htcount,hzcard,htcard] at hcG
  rw [hcG,hcE]
  ring
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
