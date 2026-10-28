module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryQuotient
public import Theory.Mathieu.M24.LargeElementaryPerfectNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# The actual moved module in the ordinary central quotient

The original module image is elementary and equals its commutator with
the source span image. A smaller-than-64 image has automorphism group of
order not divisible by 6048, so the unitary residual acts trivially, contrary
to full movement and noncentrality. Thus this literal image has at least
64 elements. The native M₂₄ large-elementary normalizer obstruction then
excludes M₂₄, with the same perfect span image and radical convention.

Source: Aschbacher–Smith C.3.1–5, pp.149–150, and 4.2.12–13, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

private theorem small_elementary_aut_order_not_dvd
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E < 64) : ¬ 6048 ∣ Nat.card (MulAut E) := by
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hdim : d < 6 := by
    rw [hd] at hc
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

/-- The literal image of the source module in the ordinary central quotient
has at least 64 elements; its full action and original span are retained. -/
theorem unitary_ordinary_module_image
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    let q := QuotientGroup.mk' (center K)
    let B := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map q
    let E := ((V.subgroupOf H).subgroupOf K).map q
    Group.IsPerfect B ∧ IsElementaryAbelian 2 E ∧
      B ≤ normalizer (E : Set (K ⧸ center K)) ∧
      E = ⁅E,B⁆ ∧ 64 ≤ Nat.card E ∧ 6048 ∣ Nat.card B := by
  let X := conjugateSpanBy L M
  let A := (X.subgroupOf H).subgroupOf K
  let U := (V.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let B := A.map q
  let E := U.map q
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hVH : V ≤ H := h.module_le.trans hXH
  have hVK : V.subgroupOf H ≤ K := (subgroupOf_mono H h.module_le).trans (h.ordinary_span_le K hK)
  let e : A ≃* X := (subgroupOfEquivOfLe (h.ordinary_span_le K hK)).trans
    (subgroupOfEquivOfLe hXH)
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  let := h.module_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hfull : U = ⁅U,A⁆ := by
    apply map_injective K.subtype_injective
    apply map_injective H.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hVK,
      map_subgroupOf_eq_of_le (h.ordinary_span_le K hK),
      map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hXH]
    exact h.module_commutator
  have hEB : E = ⁅E,B⁆ := by
    simpa only [map_commutator] using congrArg (fun U : Subgroup K => U.map q) hfull
  have hBN : B ≤ normalizer (E : Set (K ⧸ center K)) :=
    le_normalizer_iff_commutator_le_left.mpr hEB.symm.le
  have hne : E ≠ ⊥ := by
    intro he
    have hUZ : U ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff U).mp he
    apply h.ordinary_module_not_centralizes K hK
    intro v hv k hk
    have hz := hUZ (show (⟨v,hVK hv⟩ : K) ∈ U from hv)
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨k,hk⟩)
  refine ⟨inferInstance,inferInstance,hBN,hEB,?_,h.unitary_ordinary_image_order_dvd a K hK⟩
  by_contra! hsmall
  let f : X →* B := (q.subgroupMap A).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp e.symm.surjective
  let b : B →* normalizer (E : Set (K ⧸ center K)) := inclusion hBN
  let ρ := E.normalizerMonoidHom.comp (b.comp f)
  have hz := h.unitary_span_hom_eq_one_of_order_not_dvd a
    (small_elementary_aut_order_not_dvd E hsmall) ρ
  have hcent : B ≤ centralizer (E : Set (K ⧸ center K)) := by
    intro y hy
    obtain ⟨x,hx⟩ := hf ⟨y,hy⟩
    have hid : b ⟨y,hy⟩ ∈ E.normalizerMonoidHom.ker := by
      change E.normalizerMonoidHom (b ⟨y,hy⟩) = 1
      rw [← hx]
      exact DFunLike.congr_fun hz x
    rw [E.normalizerMonoidHom_ker] at hid
    exact hid
  exact hne (hEB.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)))

theorem no_unitary_ordinary_mathieu24
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M24) : False := by
  obtain ⟨hb,he,hn,_,hc,hd⟩ := h.unitary_ordinary_module_image a K hK
  let B := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let E := ((V.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let := hb
  let := he
  let : Group.IsPerfect (B.map e.toMonoidHom) := Group.IsPerfect.map _
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map _
  apply Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.no_perfect_large_elementary_normalizer
    (B.map e.toMonoidHom) (E.map e.toMonoidHom)
    ((map_mono hn).trans (E.le_normalizer_map e.toMonoidHom))
  · rwa [card_map_of_injective e.injective]
  · rw [card_map_of_injective e.injective]
    exact (by decide : 63 ∣ 6048).trans hd
end CFSG.Quasithin.ChapterC.HypothesisC28
