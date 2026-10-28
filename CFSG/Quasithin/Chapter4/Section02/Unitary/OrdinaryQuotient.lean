module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FiniteExclusions
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient

/-!
# The original unitary section in an ordinary component quotient

The source span maps nontrivially into the ordinary component modulo its
center. Its simple G₂(2)′ section forces 6048 to divide the order of this
literal image. The quotient has strictly larger order: equality would make
the image the whole simple group, normalizing the nonidentity image of the
source radical, a two-group. These bounds are used in the ordinary catalogue
inspection, including the equal-order binary derived G₂ row.

Source: Aschbacher–Smith C.3.2–5, pp.149–150, and 4.2.12–13, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

theorem unitary_ordinary_image_order_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    6048 ∣ Nat.card ((((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
      (QuotientGroup.mk' (center K))) := by
  let X := conjugateSpanBy L M
  let A := (X.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let e : A ≃* X := (subgroupOfEquivOfLe (h.ordinary_span_le K hK)).trans
    (subgroupOfEquivOfLe hXH)
  let f : X →* A.map q := (q.subgroupMap A).comp e.symm.toMonoidHom
  by_contra hd
  have hf := h.unitary_span_hom_eq_one_of_order_not_dvd a hd f
  apply h.ordinary_module_not_centralizes K hK
  intro v hv k hk
  let x : X := ⟨v.val,h.module_le hv⟩
  have hx := congrArg Subtype.val (DFunLike.congr_fun hf x)
  have hz : ((e.symm x : A) : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  exact congrArg K.subtype (mem_center_iff.mp hz ⟨k,hk⟩)

theorem unitary_ordinary_order_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    6048 ∣ Nat.card (K ⧸ center K) :=
  (h.unitary_ordinary_image_order_dvd a K hK).trans (card_subgroup_dvd_card _)

theorem unitary_ordinary_order_gt
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    6048 < Nat.card (K ⧸ center K) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨_,hP,hne,hn,_⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let P := ((R.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  have hc : 6048 ≤ Nat.card A := Nat.le_of_dvd Nat.card_pos
    (h.unitary_ordinary_image_order_dvd a K hK)
  by_contra! hb
  have ht : A = ⊤ := A.eq_top_of_card_eq (Nat.le_antisymm (card_le_card_group A) (hb.trans hc))
  have hN : P.Normal := normalizer_eq_top_iff.mp (top_unique (ht ▸ hn))
  let := hN
  have hPt : P = ⊤ := hN.eq_bot_or_eq_top.resolve_left hne
  have hp : IsPGroup 2 (K ⧸ center K) := by
    change IsPGroup 2 P at hP
    rw [hPt] at hP
    exact hP.of_equiv topEquiv
  have hd := h.unitary_ordinary_order_dvd a K hK
  obtain ⟨n,hh⟩ := hp.exists_card_eq
  rw [hh] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow ((by decide : 3 ∣ 6048).trans hd))
end CFSG.Quasithin.ChapterC.HypothesisC28
