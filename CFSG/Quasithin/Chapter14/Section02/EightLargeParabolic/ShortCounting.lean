module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortExtension
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortBender

/-!
# Unique fixed cosets for the full binary short centralizer

Every involution in either enlarged endpoint lies in its original marked
endpoint. The literal endpoint fusion identifies both commuting-class fibers
with their native counterparts. The centralizer and endpoint indices agree,
so the common cubic factor cancels in the incidence count. Ambient short-root
extremality supplies a fixed coset; equality of the total count makes it unique.

This proves the counting step of Aschbacher--Smith F.4.42, printed p.295,
including the original cubic case of 14.2.18 and 14.3.15, pp.987,994
(`refs/quasithin.pdf`). No whole-group model equivalence is assumed.
The literal component application is TerminalSolvable/EightBorelShortExtension.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one

private theorem conj_order {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private def classRestriction {G : Type*} [Group G] (A B : Subgroup G)
    (p : G → Prop) (hAB : A ≤ B) (h : ∀ x : B, p x.val → x.val ∈ A) :
    {x : B // p x.val} ≃ {x : A // p x.val} where
  toFun x := ⟨⟨x.val.val,h x.val x.property⟩,x.property⟩
  invFun x := ⟨⟨x.val.val,hAB x.val.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def subgroupOfInfEquiv {G : Type*} [Group G] (A B : Subgroup G) :
    A.subgroupOf B ≃* (A ⊓ B : Subgroup G) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem fusion_all {G E : Type*} [Group G] [Group E]
    (A B : Subgroup G) (f : A →* E) (g : B →* E)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (t : A) (ht : orderOf t.val = 2)
    (hfusion : ∀ y : B, orderOf y.val = 2 →
      (IsConj t.val y.val ↔ IsConj (f t) (g y))) (y : B) :
    IsConj t.val y.val ↔ IsConj (f t) (g y) := by
  constructor
  · intro h
    exact (hfusion y ((conj_order h).symm.trans ht)).mp h
  · intro h
    have hy : orderOf y.val = 2 := by
      rw [Subgroup.orderOf_coe,←orderOf_injective g hg]
      exact (conj_order h).symm.trans
        ((orderOf_injective f hf t).trans ((Subgroup.orderOf_coe t).symm.trans ht))
    exact (hfusion y hy).mpr h

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
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

/-- Unique fixed cosets in the original full short centralizer, including
the cubic endpoint extension. The matching cubic indices cancel in the
commuting-involution incidence comparison. -/
theorem source_short_unique_fixed (r : MarkedTriality T M Mc H)
    (d : ExtensionField P) (hd : d ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    let C := centralizer ({(markedShortRoot r d : G)} : Set G)
    ∀ x : C, IsConj z (x : G) →
      ∃! q : C ⧸ M.subgroupOf C, x • q = q := by
  let L := secondParabolic T M Mc H
  let t : G := markedShortRoot r d
  let C := centralizer ({t} : Set G)
  let X := M.subgroupOf C
  let X₀ := L.subgroupOf C
  let f : L →* Carrier P := (parabolic P .central).subtype.comp r.right.toMonoidHom
  let g : H →* Carrier P := (parabolic P .arms).subtype.comp r.left.toMonoidHom
  have hf : Function.Injective f := (parabolic P .central).subtype_injective.comp r.right.injective
  have hg : Function.Injective g := (parabolic P .arms).subtype_injective.comp r.left.injective
  have hzH : z ∈ H := hH.1.1.2 (centralInvolutions_le_sylow T hz)
  let zH : H := ⟨z,hzH⟩
  let ze := g zH
  let te := f (markedShortRoot r d)
  have ht2 : orderOf t = 2 := markedShortRoot_order r d hd
  have hz2 : orderOf z = 2 := by
    have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
    have hn : (⟨z,hz⟩ : centralInvolutions T) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    exact (Subgroup.orderOf_coe ⟨z,hz⟩).trans
      (orderOf_eq_prime (by
        have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : centralInvolutions T))
        rwa [hc] at hh) hn)
  have hCz : centralizer ({z} : Set G) = Mc :=
    (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1).symm
  have hmodelZ : centralizer ({ze} : Set (Carrier P)) = parabolic P .arms := by
    rw [highestRoot_centralizer_eq_localFactor 1 Nat.zero_lt_one ze
      (marked_core_center_mem r zH (by rwa [source_firstCore_center hG hempty hM hu hmany hcard e hH r]))
      (fun hh => hz1 (congrArg Subtype.val (hg (hh.trans g.map_one.symm)))),
      parabolic_arms_eq_localFactor_at_two P rfl (by simp only [binaryParameters_q,pow_one])]
  let eZ := r.left.trans (MulEquiv.subgroupCongr hmodelZ.symm)
  let eX := (shortLocalEquiv r d).symm.trans (markedShortCentralizerEquiv r d hd)
  have hte : te = RadicalCoordinates.LeviCommutators.short P rfl 2 d := markedShortRoot_image r d
  have hfirst := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hLM : L ≤ M := (source_parabolics hG T hempty hM hu hmany hcard e H hH
    (firstResidualQuotientEquiv r)).2.2.2.2
  have hiv := source_endpoint_involutions hG hempty hM hu hmany hcard e hH r
  have hZ (y : H) : IsConj t y.val ↔ IsConj te (g y) := by
    apply fusion_all L H f g hf hg (markedShortRoot r d) ht2
    intro y hy
    exact ⟨fun hc => ((source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r
      y (markedShortRoot r d) hy ht2).mp hc.symm).symm,
      fun hc => ((source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r
        y (markedShortRoot r d) hy ht2).mpr hc.symm).symm⟩
  have hX (y : L) : IsConj z y.val ↔ IsConj ze (f y) :=
    fusion_all H L g f hg hf zH hz2
      (fun y hy => source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r
        zH y hz2 hy) y
  have hfZ : Nat.card (CommutingClassIncidence.Fiber z t) =
      Nat.card (CommutingClassIncidence.Fiber ze te) := by
    let j := classRestriction H (centralizer ({z} : Set G)) (fun y => IsConj t y)
      (hCz.symm ▸ hfirst) (fun x hx => hiv.1 x.val (hCz ▸ x.property)
        ((conj_order hx).symm.trans ht2))
    exact (Nat.card_congr j).trans (Nat.card_congr
      (eZ.toEquiv.subtypeEquiv (fun y => hZ y)))
  have hfX : Nat.card {a : X // IsConj z a.val.val} =
      Nat.card (CommutingClassIncidence.Fiber te ze) := by
    let j := classRestriction X₀ X (fun y : C => IsConj z y.val)
      (fun _ hy => hLM hy) (fun y hy => hiv.2 y.val.val y.property
        ((conj_order hy).symm.trans hz2))
    rw [hte]
    exact (Nat.card_congr j).trans (Nat.card_congr
      (eX.toEquiv.subtypeEquiv (fun y => hX ⟨y.val.val,y.property⟩)))
  have hcZ : Nat.card H = Nat.card (centralizer ({ze} : Set (Carrier P))) :=
    Nat.card_congr eZ.toEquiv
  have hcX : Nat.card X₀ = Nat.card (centralizer ({te} : Set (Carrier P))) := by
    rw [hte]
    exact Nat.card_congr eX.toEquiv
  have hidx : (L ⊓ C).relIndex (M ⊓ C) = H.relIndex Mc :=
    (source_short_centralizer_index hG hempty hM hu hmany hcard e hH r d hd).trans
      (source_endpoint_indices hG hempty hM hu hmany hcard e hH r)
  have hcardX : Nat.card X₀ * H.relIndex Mc = Nat.card X := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (L ⊓ C) (M ⊓ C)
      bot_le (inf_le_inf_right C hLM)
    simp only [relIndex_bot_left,hidx] at hh
    rwa [←Nat.card_congr (subgroupOfInfEquiv L C).toEquiv,
      ←Nat.card_congr (subgroupOfInfEquiv M C).toEquiv] at hh
  have hcardZ : Nat.card H * H.relIndex Mc = Nat.card (centralizer ({z} : Set G)) := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) H Mc bot_le hfirst
    simpa only [relIndex_bot_left,hCz] using hh
  have hlocal : Nat.card (centralizer ({z} : Set G)) *
        Nat.card {a : X // IsConj z a.val.val} =
      Nat.card X * Nat.card (CommutingClassIncidence.Fiber z t) := by
    rw [←hcardZ,←hcardX,hfX,hfZ,hcZ,hcX]
    have he := CommutingClassIncidence.balance ze te
    calc
      _ = (Nat.card (centralizer ({ze} : Set (Carrier P))) *
          Nat.card (CommutingClassIncidence.Fiber te ze)) * H.relIndex Mc := by ring
      _ = _ := by rw [he]; ring
  have hcount : Nat.card {a : C // IsConj z a.val} * Nat.card X =
      Nat.card C * Nat.card {a : X // IsConj z a.val.val} := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := centralizer ({z} : Set G)))
    have he := CommutingClassIncidence.balance z t
    change Nat.card (centralizer ({z} : Set G)) *
      (Nat.card (CommutingClassIncidence.Fiber t z) * Nat.card X) = _
    calc
      _ = (Nat.card (centralizer ({z} : Set G)) *
        Nat.card (CommutingClassIncidence.Fiber t z)) * Nat.card X := by ring
      _ = _ := by rw [he]; change Nat.card C * _ * _ = _; rw [mul_assoc, mul_comm (Nat.card (CommutingClassIncidence.Fiber z t)),←hlocal]; ring
  apply UniqueFixedCoset.unique_of_class_count X (fun a : C => IsConj z a.val) _ _ hcount
  · intro a b
    have hh : IsConj b.val ((a*b*a⁻¹ : C) : G) := isConj_iff.mpr ⟨a.val,rfl⟩
    exact ⟨fun h => h.trans hh.symm,fun h => h.trans hh⟩
  · intro a ha
    have ha2 : orderOf a = 2 := by
      rw [←Subgroup.orderOf_coe]
      exact (conj_order ha).symm.trans hz2
    have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,ha2,pow_one])
    obtain ⟨R,hR⟩ := hp.exists_le_sylow
    obtain ⟨S,hS⟩ := source_short_ambient_sylow hG hempty hM hu hmany hcard e hH r d hd
    obtain ⟨a',ha'⟩ := MulAction.exists_smul_eq C R S
    have hga : a'*a*a'⁻¹ ∈ X := by
      apply hLM
      apply (show (T : Subgroup G) ≤ L from le_sup_right.trans le_sup_left)
      change a'*a*a'⁻¹ ∈ (T : Subgroup G).subgroupOf C
      rw [←hS,←ha']
      exact mem_map_of_mem (MulAut.conj a').toMonoidHom (hR (mem_zpowers a))
    refine ⟨QuotientGroup.mk a'⁻¹,?_⟩
    rw [MulAction.Quotient.smul_mk,QuotientGroup.eq]
    change (a*a'⁻¹)⁻¹*a'⁻¹ ∈ X
    convert X.inv_mem hga using 1
    group

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
