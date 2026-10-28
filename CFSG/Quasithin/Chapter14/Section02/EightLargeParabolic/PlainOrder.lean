module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortBender
public import Theory.GroupTheory.InvolutionClassOrderComparison

/-!
# Thompson order comparison for the original plain triality endpoints

When Mc equals the first endpoint, both full ambient involution centralizers
have the native markings already proved by F.4.42. Their distinguished
involutions and ambient fusion agree under the same literal endpoint maps.
Thompson's mixed-pair fibers therefore agree, so the two-class order formula
identifies the order of G with the native triality order.

The native class catalogue is recovered by conjugating into its positive
Sylow and lifting through the original marking. No ambient equivalence,
order bound or sixth-power relation is assumed. The application to the
original component and the resulting small completion is EightBorelOrder.
Source: Aschbacher--Smith F.4.43, printed p.296, in the Mc = H branch of
14.2.18--19 and 14.3.15, printed pp.987,994.
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

private def ambientCentralizerEquiv (L : Subgroup G) (t : L)
    (hC : centralizer ({(t : G)} : Set G) ≤ L) :
    centralizer ({(t : G)} : Set G) ≃* centralizer ({t} : Set L) where
  toFun x := ⟨⟨x,hC x.property⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨x.val.val,mem_centralizer_singleton_iff.mpr
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

/-- F.4.43 on the original ambient group in the plain partner branch. -/
theorem source_card_eq_triality_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) : Nat.card G = Nat.card (Carrier P) := by
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
  have hCz : centralizer ({(z : G)} : Set G) = H :=
    (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r z.property hz1).symm.trans hplain
  have hCze : centralizer ({ze} : Set (Carrier P)) = parabolic P .arms := by
    rw [←hzmark,highestRoot_centralizer_eq_localFactor 1 Nat.zero_lt_one (f zH)
      (marked_core_center_mem r zH (by rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]; exact z.property))
      (fun hh => hz1 (congrArg Subtype.val (hf (hh.trans f.map_one.symm)))),
      parabolic_arms_eq_localFactor_at_two P rfl (by simp only [binaryParameters_q,pow_one])]
  let eZ : centralizer ({(z : G)} : Set G) ≃* centralizer ({ze} : Set (Carrier P)) :=
    (MulEquiv.subgroupCongr hCz).trans (r.left.trans (MulEquiv.subgroupCongr hCze.symm))
  have heZ (x : centralizer ({(z : G)} : Set G)) : (eZ x).val = f ⟨x,hCz.le x.property⟩ := rfl
  have hCt := source_short_centralizer_le_of_partner_eq hG hempty hM hu hmany hcard e hH
    r hplain 1 one_ne_zero
  let eT : centralizer ({(t : G)} : Set G) ≃* centralizer ({te} : Set (Carrier P)) :=
    (ambientCentralizerEquiv L t hCt).trans ((markedShortCentralizerEquiv r 1 one_ne_zero).trans
      (MulEquiv.subgroupCongr (congrArg (fun u : Carrier P => centralizer ({u} : Set (Carrier P)))
        (markedShortRoot_image r 1).symm)))
  have heT (x : centralizer ({(t : G)} : Set G)) : (eT x).val = g ⟨x,hCt x.property⟩ := rfl
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
  have hzcount := InvolutionClassOrderComparison.kappa_eq
    (z:G) (t:G) (z:G) ze te ze hz2 ht hneq hze hte hneqe eZ
    (by
      apply Subtype.ext
      exact (heZ _).trans ((congrArg f
        (show (⟨_,hCz.le (centralizerPoint (z:G)).property⟩ : H) = zH from
          Subtype.ext (centralizerPoint_coe _))).trans
            (hzmark.trans (centralizerPoint_coe _).symm)))
    (fun a => by rw [heZ]; exact hfusionH zL hz2 ⟨a,hCz.le a.property⟩)
    (fun a => by rw [heZ]; exact hfusionH t ht ⟨a,hCz.le a.property⟩)
  have htcount := InvolutionClassOrderComparison.kappa_eq
    (z:G) (t:G) (t:G) ze te te hz2 ht hneq hze hte hneqe eT
    (by
      apply Subtype.ext
      exact (heT _).trans ((congrArg g
        (show (⟨_,hCt (centralizerPoint (t:G)).property⟩ : L) = t from
          Subtype.ext (centralizerPoint_coe _))).trans
            (centralizerPoint_coe _).symm))
    (fun a => by rw [heT]; exact hfusionL zL hz2 ⟨a,hCt a.property⟩)
    (fun a => by rw [heT]; exact hfusionL t ht ⟨a,hCt a.property⟩)
  have hzcard := Nat.card_congr eZ.toEquiv
  have htcard := Nat.card_congr eT.toEquiv
  have hcG := TwoInvolutionClassOrder.card_eq (z:G) (t:G) hz2 ht hneq hclasses
  have hcE := TwoInvolutionClassOrder.card_eq ze te hze hte hneqe hclassesE
  rw [hzcount,htcount,hzcard,htcard] at hcG
  exact hcG.trans hcE.symm
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
