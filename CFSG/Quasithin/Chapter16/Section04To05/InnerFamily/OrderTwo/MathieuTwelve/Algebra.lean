module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection


/-!
# Ambient calculations for the M₁₂ branch of 16.4.9(1)

An inner element of R has actual multiplication coordinates in T_L T_C:
Sylow intersection with the two relatively normal factors gives the coordinates,
and tight embedding places the commuting coordinate in N_TC(K′). A marked
non-two-central coset then gives the cover contradiction from I.2.2(5b).

In the centerless case the model commutator identity forces the component
coordinate into R, so faithfulness kills the commuting coordinate. The earlier
normalizer equality and equivalence then give T_C = C_TC(R) of elementary
order four. The automorphism-generation calculation makes T_C central in T;
the same commutator identity supplies the noncommuting witness for the final
Sylow-centralizer contradiction.

The mark and the model identities are explicit hypotheses of these ambient
lemmas. They remain separate proof obligations; this module does not assert
the M₁₂ branch of the source theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.9(1), printed p.1189, case (III); I.2.2(5b), p.409.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve
open OuterResidual DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The missing model mark, in the actual central quotient and residual centralizer. -/
def MarkedResidualInvolution (L : Subgroup G) (r : G) : Prop :=
  ∃ u : L ⧸ center L, orderOf u = 2 ∧ ¬ TwoCentral u ∧
    (centerQuotientEquivActionImage L u : ActionQuotient L) ∈ residualCentralizer L r

/-- Equality of orders lifts the actual marked residual-centralizer element to R. -/
theorem lift_marked_residual_involution (h : IntersectionSetup T z L g R)
    (hres : involutionResidual L r ≤ L.conjBy g)
    (hc : Nat.card R = Nat.card (residualCentralizer L r))
    (hm : MarkedResidualInvolution L r) :
    ∃ s : R, ∃ u : L ⧸ center L, orderOf (s : G) = 2 ∧ ¬ TwoCentral u ∧
      (centerQuotientEquivActionImage L u : ActionQuotient L) =
        actionMap (h.le_sylow.trans h.sylow_normalizes) s := by
  obtain ⟨u, hu2, hum, huC⟩ := hm
  let e := residualCentralizerEquiv h hres hc
  let uC : residualCentralizer L r := ⟨_, huC⟩
  refine ⟨e.symm uC, u, ?_, hum, ?_⟩
  · have ho : orderOf uC = 2 := by
      calc
        orderOf uC = orderOf (uC : ActionQuotient L) := (orderOf_coe uC).symm
        _ = orderOf (centerQuotientEquivActionImage L u) := orderOf_coe (centerQuotientEquivActionImage L u)
        _ = 2 := ((centerQuotientEquivActionImage L).orderOf_eq u).trans hu2
    exact (orderOf_coe _).trans ((e.symm.orderOf_eq uC).trans ho)
  · exact (congrArg Subtype.val (e.apply_symm_apply uC)).symm

private theorem sylow_inf_sup_normal (P : Sylow 2 G) (K D : Subgroup G)
    [K.Normal] [D.Normal] :
    (P : Subgroup G) ⊓ (K ⊔ D) =
      ((P : Subgroup G) ⊓ K) ⊔ ((P : Subgroup G) ⊓ D) := by
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal K
  let q := QuotientGroup.mk' D
  have hmap := P.map_image_eq_inf K ((P : Subgroup G) ⊓ K) Q hQ inf_le_left q
  apply le_antisymm
  · intro x hx
    have himg : q x ∈ K.map q := by
      have hm := mem_map_of_mem q hx.2
      simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] using hm
    have hximg : q x ∈ ((P : Subgroup G) ⊓ K).map q := by
      rw [hmap]
      exact ⟨mem_map_of_mem q hx.1, himg⟩
    obtain ⟨k, hk, he⟩ := hximg
    have hd : k⁻¹ * x ∈ D := by
      apply (QuotientGroup.eq_one_iff (k⁻¹ * x)).mp
      change q (k⁻¹ * x) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [show x = k * (k⁻¹ * x) from (mul_inv_cancel_left k x).symm]
    exact mul_mem_sup hk ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hk.1) hx.1, hd⟩
  · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)

/-- An inner quotient image places the original element in C_G(L)L. -/
theorem mem_inner_product_of_action (h : IntersectionSetup T z L g R)
    (s : R) (hs : actionMap (h.le_sylow.trans h.sylow_normalizes) s ∈ actionImage L L) :
    (s : G) ∈ centralizer (L : Set G) ⊔ L := by
  obtain ⟨v, hv, he⟩ := hs
  have hk' : (⟨s, h.sylow_normalizes (h.le_sylow s.property)⟩ : normalizer (L : Set G)) / v ∈
      (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) :=
    QuotientGroup.eq_iff_div_mem.mp he.symm
  have hk : (s : G) / (v : G) ∈ centralizer (L : Set G) := hk'
  have hm : (s : G) / (v : G) * (v : G) ∈ centralizer (L : Set G) ⊔ L :=
    (centralizer (L : Set G) ⊔ L).mul_mem (mem_sup_left hk) (mem_sup_right hv)
  simpa only [div_mul_cancel] using hm

/-- Sylow intersection distributes over the two relatively normal factors K and L. -/
theorem inner_sylow_product (h : IntersectionSetup T z L g R) :
    (T : Subgroup G) ⊓ (centralizer (L : Set G) ⊔ L) =
      commutingSylow T L ⊔ componentSylow T L := by
  let H := normalizer (L : Set G)
  let K := centralizer (L : Set G)
  let P := T.subtype h.sylow_normalizes
  let K₀ := K.subgroupOf H
  let L₀ := L.subgroupOf H
  have hKH : K ≤ H := centralizer_le_normalizer _
  have hLH : L ≤ H := L.le_normalizer
  let : K₀.Normal := normal_subgroupOf_centralizer_normalizer (L : Set G)
  let : L₀.Normal := normal_in_normalizer
  have he := sylow_inf_sup_normal P K₀ L₀
  apply le_antisymm
  · intro s hs
    have hsH : s ∈ H := h.sylow_normalizes hs.1
    have hs₀ : (⟨s, hsH⟩ : H) ∈ (P : Subgroup H) ⊓ (K₀ ⊔ L₀) := by
      refine ⟨hs.1, ?_⟩
      rw [← subgroupOf_sup hKH hLH]
      exact hs.2
    rw [he] at hs₀
    have hm := mem_map_of_mem H.subtype hs₀
    rw [Subgroup.map_sup] at hm
    exact (sup_le_sup
      (show ((P : Subgroup H) ⊓ K₀).map H.subtype ≤ commutingSylow T L from
        by rintro x ⟨a, ha, rfl⟩; exact ⟨ha.1, ha.2⟩)
      (show ((P : Subgroup H) ⊓ L₀).map H.subtype ≤ componentSylow T L from
        by rintro x ⟨a, ha, rfl⟩; exact ⟨ha.1, ha.2⟩)) hm
  · exact sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))

/-- Construct both coordinates and place the commuting one in N_TC(K′). -/
theorem inner_factorization (h : IntersectionSetup T z L g R) (s : R)
    (hs2 : orderOf (s : G) = 2)
    (hs : actionMap (h.le_sylow.trans h.sylow_normalizes) s ∈ actionImage L L) :
    ∃ v ∈ componentSylow T L, ∃ c ∈ commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G), (s : G) = v * c := by
  have hsprod : (s : G) ∈ commutingSylow T L ⊔ componentSylow T L := by
    rw [← inner_sylow_product h]
    exact ⟨h.le_sylow s.property, mem_inner_product_of_action h s hs⟩
  have hcomm : commutingSylow T L ≤ centralizer (componentSylow T L : Set G) :=
    inf_le_right.trans (centralizer_le inf_le_right)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (hcomm.trans (centralizer_le_normalizer _))] at hsprod
  obtain ⟨c, hc, v, hv, he⟩ := hsprod
  have hvc : Commute v c := mem_centralizer_iff.mp hc.2 v hv.2
  have hsC : c ∈ involutionCentralizer (s : G) := by
    apply mem_centralizer_iff.mpr
    rintro x (rfl : x = (s : G))
    rw [← he]
    exact (Commute.refl c |>.mul_left hvc).eq
  exact ⟨v, hv, c, ⟨hc, centralizer_le_conjugate_normalizer h s.property hs2 hsC⟩,
    he.symm.trans hvc.eq.symm⟩

/-- The component coordinate represents the original marked central coset. -/
theorem component_coset_eq (h : IntersectionSetup T z L g R) (s : R)
    (u : L ⧸ center L)
    (hu : (centerQuotientEquivActionImage L u : ActionQuotient L) =
      actionMap (h.le_sylow.trans h.sylow_normalizes) s)
    (v : L) {c : G} (hc : c ∈ centralizer (L : Set G))
    (he : (s : G) = v * c) : QuotientGroup.mk' (center L) v = u := by
  apply (centerQuotientEquivActionImage L).injective
  apply Subtype.ext
  change actionElement L v (L.le_normalizer v.property) = _
  rw [hu]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (v : G) / s ∈ centralizer (L : Set G)
  have hvc : Commute (v : G) c := mem_centralizer_iff.mp hc v v.property
  have hd : (v : G) / s = c⁻¹ := by
    rw [he, hvc.eq]
    simp only [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hd]
  exact (centralizer (L : Set G)).inv_mem hc

/-- The double-cover contradiction from the marked coset and the exact I.2.2 lifting input. -/
theorem cover_contradiction (h : IntersectionSetup T z L g R)
    (hres : involutionResidual L r ≤ L.conjBy g)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (hc : Nat.card R = Nat.card (residualCentralizer L r))
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    (hZ : Nat.card (center L) = 2) (hlift : NonTwoCentralInvolutionLifting L)
    (hm : MarkedResidualInvolution L r) : False := by
  obtain ⟨s, u, hs2, hum, hu⟩ := lift_marked_residual_involution h hres hc hm
  have hsinner : actionMap (h.le_sylow.trans h.sylow_normalizes) s ∈ actionImage L L :=
    hu ▸ (centerQuotientEquivActionImage L u).property
  obtain ⟨v, hv, c, hc, he⟩ := inner_factorization h s hs2 hsinner
  have hq := component_coset_eq h s u hu ⟨v, hv.2⟩ hc.1.2 he
  have hu2 : orderOf u = 2 := by
    have hsimg := orderOf_injective (actionMap (h.le_sylow.trans h.sylow_normalizes))
      (actionMap_injective _ (faithful h)) s
    rw [← hu, orderOf_coe, MulEquiv.orderOf_eq, ← orderOf_coe] at hsimg
    exact hsimg.trans hs2
  have hv4 : orderOf v = 4 := by
    apply (orderOf_coe (⟨v, hv.2⟩ : L)).trans
    apply order_four_of_marked_coset hZ hlift ⟨v, hv.2⟩
    · rwa [hq]
    · rwa [hq]
  exact no_order_four_component_lift h hres e hs2 hc hv.2 he hv4

/-- Generation of H by KL and r gives the actual product T = TC TL R. -/
theorem sylow_generation (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hgen : normalizer (L : Set G) ≤ (centralizer (L : Set G) ⊔ L) ⊔ zpowers r) :
    (T : Subgroup G) = (commutingSylow T L ⊔ componentSylow T L) ⊔ R := by
  apply le_antisymm
  · intro x hx
    have hm := hgen (h.sylow_normalizes hx)
    have hn : zpowers r ≤ normalizer ((centralizer (L : Set G) ⊔ L : Subgroup G) : Set G) :=
      (zpowers_le.mpr hr).trans ((h.sylow.le.trans inf_le_right).trans
        (normalizer_le_componentProduct_normalizer h.normalizers_eq))
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hn] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    have hbR : b ∈ R := zpowers_le.mpr hr hb
    have haT : a ∈ (T : Subgroup G) := by
      simpa only [mul_inv_cancel_right] using T.mul_mem hx (T.inv_mem (h.le_sylow hbR))
    have haI : a ∈ commutingSylow T L ⊔ componentSylow T L := by
      rw [← inner_sylow_product h]
      exact ⟨haT, ha⟩
    exact mul_mem_sup haI hbR
  · exact sup_le (sup_le inf_le_left inf_le_left) h.le_sylow

/-- Tight embedding and 16.4.2(3) place the Sylow-centralizer commutator in R. -/
theorem sylow_centralizer_commutator_le (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) {s : G} (hs : s ∈ R) (hs2 : orderOf s = 2) :
    ⁅componentSylow T L ⊓ involutionCentralizer s, zpowers r⁆ ≤ R := by
  rw [h.eq_intersection]
  refine le_inf ?_ ((commutator_le_sup _ _).trans
    (sup_le (inf_le_left.trans inf_le_left) ((zpowers_le.mpr hr).trans h.le_sylow)))
  apply le_trans (commutator_mono le_rfl
    ((zpowers_le.mpr hr).trans (h.sylow.le.trans inf_le_left)))
  exact le_normalizer_iff_commutator_le_right.mp
    (inf_le_right.trans (centralizer_le_conjugate_normalizer h hs hs2))

/-- The model identity forces s = sL: its other coordinate lies in R ∩ K = 1. -/
theorem component_eq_of_sylow_commutator (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) {s v c : G} (hs : s ∈ R) (hs2 : orderOf s = 2)
    (hc : c ∈ centralizer (L : Set G)) (he : s = v * c)
    (hcomm : zpowers v = ⁅componentSylow T L ⊓ involutionCentralizer s, zpowers r⁆) :
    s = v := by
  have hvR : v ∈ R := by
    apply (sylow_centralizer_commutator_le h hr hs hs2)
    rw [← hcomm]
    exact mem_zpowers v
  have hcR : c ∈ R := by
    have hm := R.mul_mem (R.inv_mem hvR) hs
    rwa [he, inv_mul_cancel_left] at hm
  have hc1 : c = 1 := Subgroup.disjoint_def.mp (faithful h) hcR hc
  simpa only [hc1, mul_one] using he

/-- An involution in R ∩ L makes TC equal to its centralizer of R. -/
theorem commutingSylow_eq_centralizer (h : IntersectionSetup T z L g R)
    (hn : commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    {s : G} (hs : s ∈ R) (hs2 : orderOf s = 2) (hsL : s ∈ L) :
    commutingSylow T L = commutingSylow T L ⊓ centralizer (R : Set G) := by
  rw [← hn]
  apply (inf_eq_left.mpr _).symm
  apply le_trans _ (centralizer_le_conjugate_normalizer h hs hs2)
  exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hsL))

/-- The earlier relative-normalizer equivalence gives the actual elementary order-four TC. -/
theorem commutingSylow_structure (h : IntersectionSetup T z L g R)
    (hres : involutionResidual L r ≤ L.conjBy g)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    (hc : Nat.card R = 4)
    {s : G} (hs : s ∈ R) (hs2 : orderOf s = 2) (hsL : s ∈ L) :
    Nat.card (commutingSylow T L) = 4 ∧ IsElementaryAbelian 2 (commutingSylow T L) := by
  have hn : commutingSylow T L ≤
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) :=
    (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hsL))).trans
      (centralizer_le_conjugate_normalizer h hs hs2)
  have hp (x : commutingSylow T L) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact normalizer_factor_pow_two h hres e ⟨x.property, hn x.property⟩
  refine ⟨?_, ?_⟩
  · have he := Nat.card_congr e.toEquiv
    rw [inf_eq_left.mpr hn, hc] at he
    exact he.symm
  · exact { is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
              (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
            exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

omit [Finite G] in
/-- The product generation and elementary TC make TC central in T. -/
theorem commutingSylow_central (hgen : (T : Subgroup G) =
      (commutingSylow T L ⊔ componentSylow T L) ⊔ R)
    [IsElementaryAbelian 2 (commutingSylow T L)]
    (hc : commutingSylow T L = commutingSylow T L ⊓ centralizer (R : Set G)) :
    commutingSylow T L ≤ centralizer (T : Set G) := by
  apply le_centralizer_iff.mpr
  rw [hgen]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  · exact le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_right))
  · exact le_centralizer_iff.mp (hc ▸ inf_le_right)

omit [Finite G] in
/-- The nontrivial commutator identity constructs a Sylow-centralizer element moved by r. -/
theorem exists_noncommuting_sylow_centralizer {s r : G} (hs : s ≠ 1)
    (hcomm : zpowers s = ⁅componentSylow T L ⊓ involutionCentralizer s, zpowers r⁆) :
    ∃ x ∈ componentSylow T L ⊓ involutionCentralizer s, ¬ Commute x r := by
  classical
  by_contra hn
  have hc : (componentSylow T L ⊓ involutionCentralizer s) ≤
      centralizer (zpowers r : Set G) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hxcomm : Commute x r := by
      by_contra hh
      exact hn ⟨x, hx, hh⟩
    exact (hxcomm.symm.zpow_left n).eq
  have hb := commutator_eq_bot_iff_le_centralizer.mpr hc
  exact (zpowers_ne_bot.mpr hs) (hcomm.trans hb)

/-- Complete the centerless ambient contradiction from the two remaining model identities. -/
theorem trivial_cover_contradiction (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hres : involutionResidual L r ≤ L.conjBy g)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (hc : Nat.card R = 4)
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    (hn : commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    (hgen : normalizer (L : Set G) ≤ (centralizer (L : Set G) ⊔ L) ⊔ zpowers r)
    {s v c : G} (hs : s ∈ R) (hs2 : orderOf s = 2)
    (hv : v ∈ L) (hcK : c ∈ centralizer (L : Set G)) (he : s = v * c)
    (hcomm : zpowers v = ⁅componentSylow T L ⊓ involutionCentralizer s, zpowers r⁆) :
    False := by
  have hsv := component_eq_of_sylow_commutator h hr hs hs2 hcK he hcomm
  have hsL : s ∈ L := hsv.symm ▸ hv
  have hC := commutingSylow_eq_centralizer h hn hs hs2 hsL
  let := (commutingSylow_structure h hres e hc hs hs2 hsL).2
  have hcentral := commutingSylow_central (sylow_generation h hr hgen) hC
  have hRP : R ≤ (T : Subgroup G) ⊓ involutionCentralizer s := by
    refine le_inf h.le_sylow ?_
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy' : y = s := Set.mem_singleton_iff.mp hy
    rw [hy']
    let f := residualCentralizerMap (h.le_sylow.trans h.sylow_normalizes)
      (centralizes_residual h hres)
    have hf := residualCentralizerMap_injective (h.le_sylow.trans h.sylow_normalizes)
      (centralizes_residual h hres) (faithful h)
    have heq : (⟨s, hs⟩ : R) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨s, hs⟩ := by
      apply hf
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val heq
  have hCP := centralizes_of_commutingSylow_central h hcentral
    (T.isPGroup'.to_le inf_le_left)
    (inf_le_right.trans (centralizer_le_conjugate_normalizer h hs hs2)) hRP
  have hs1 : s ≠ 1 := by intro he1; simp [he1] at hs2
  have hcomm' : zpowers s = ⁅componentSylow T L ⊓ involutionCentralizer s, zpowers r⁆ :=
    (congrArg zpowers hsv).trans hcomm
  obtain ⟨x, hx, hxr⟩ := exists_noncommuting_sylow_centralizer hs1 hcomm'
  exact hxr (mem_centralizer_iff.mp (hCP hr) x ⟨hx.1.1, hx.2⟩)

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve
