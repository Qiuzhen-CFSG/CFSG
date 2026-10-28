module
public import CFSG.Quasithin.Chapter12.Section06.Terminal.SymmetricProduct
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.ConjugationLocalGeometry

/-!
# Constructing the terminal critical-pair witnesses

At the full point centralizer, distinct critical endpoints have disjoint
order-two point lines. The absence of transvections on the original U_H/V₁
then forces U_gamma outside O₂(H): otherwise the inverse-conjugate module
has displacement at most one, the two point bounds make the endpoint
modules commute, and the original seed-centralizer equality contradicts
criticality. Endpoint reversal exchanges the two relative indices.

The critical edge is an H-conjugate of the original L₁T edge. Its two-core
image has order at most four and lies in the marked A₅ factor. These facts
construct a nontrivial involution b, D_H = U_H ∩ O₂(H)^g, and A₁ = V₁^g,
with |U_H:D_H| ≤ 4 and [D_H,b] ≤ A₁. The existing literal-section theorem
now gives the contradiction without assuming any of those witnesses.

The F.9 hypothesis, abelian-core containment, centralizer equality,
intersection commutativity and marked product/local-core facts remain
explicit source inputs. This is the terminal argument, not the universal
natural-module reduction.

Source: Aschbacher–Smith, F.9.13–17, printed pp.322–324, and the final
paragraph of Section12.6, printed p.838 (PDF p.855).
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Terminal
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
variable (h : D.Hypothesis)

include h in
private theorem small_commutator_le_core [IsElementaryAbelian 2 D.UH]
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e))
    (A B : Subgroup G) (hAH : A ≤ D.H) (hc : ⁅A,D.UH⁆ ≤ B)
    (hB : Nat.card B ≤ 2) : A ≤ D.QH := by
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨τ,c,_,_,_,hsmall⟩ := exists_product_section h e hplace
  intro a ha
  have hr := c.displacement_rank_le_of_commutator_bound A B ⊥ bot_le hc 1
    (by simpa only [relIndex_bot_left, pow_one] using hB) ⟨a,hAH ha⟩ ha
  exact ⟨⟨a,hAH ha⟩,hsmall ⟨a,hAH ha⟩ hr,rfl⟩

include h in
/-- At H = C_G(V₁), the critical point cannot coincide with V₁. -/
theorem critical_points_disjoint (hV : D.V ≤ D.QH) (hH : D.H = D.Gz)
    (i : h.CriticalEndpoint) : D.V₁ ⊓ i.conjugate D.V₁ = ⊥ := by
  apply inf_eq_bot_of_card_two_of_ne _ _ h.point_card
    ((card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card)
  intro he
  have hg : i.representative ∈ D.H := by
    rw [hH, ← h.normalizer_point_eq]
    exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hu : i.conjugate D.UH = D.UH :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy _ _) hg)
  apply i.noncentral
  change D.V₁ = i.conjugate D.V₁ at he
  rw [hu, ←he]
  exact (commutator_mono le_rfl hV).trans h.commutator_UH_QH_le_point

include h in
/-- The no-transvection result excludes U_gamma = D_gamma in F.9.16(1). -/
theorem critical_not_le_core (hV : D.V ≤ D.QH) (hH : D.H = D.Gz)
    (hC : centralizer (D.Vplus : Set G) = centralizer (D.V : Set G))
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e))
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) : ¬ i.conjugate D.UH ≤ D.QH := by
  let := h.UH_elementary_of_V_le_QH hV
  intro hcore
  let g := i.representative
  let A := D.UH.conjBy g⁻¹
  let B := D.V₁.conjBy g⁻¹
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hAH : A ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (hUV.trans (i.reverse_le hb))
    change A ≤ (D.H.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hcomm₁ : ⁅D.UH,i.conjugate D.UH⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl hcore).trans h.commutator_UH_QH_le_point
  have hAB : ⁅A,D.UH⁆ ≤ B := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcomm₁
    rw [map_commutator] at hh
    change ⁅A,(D.UH.conjBy g).conjBy g⁻¹⁆ ≤ B at hh
    rwa [conjBy_inv] at hh
  have hB : Nat.card B ≤ 2 :=
    ((card_map_of_injective (MulAut.conj g⁻¹).injective).trans h.point_card).le
  have hAQ := small_commutator_le_core h e hplace A B hAH hAB hB
  have hcomm₂ : ⁅D.UH,i.conjugate D.UH⁆ ≤ i.conjugate D.V₁ := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((commutator_mono le_rfl hAQ).trans h.commutator_UH_QH_le_point)
    rw [map_commutator] at hh
    change ⁅i.conjugate D.UH,(D.UH.conjBy g⁻¹).conjBy g⁆ ≤ i.conjugate D.V₁ at hh
    rw [conjBy_inv', commutator_comm] at hh
    exact hh
  have hzero : ⁅D.UH,i.conjugate D.UH⁆ = ⊥ :=
    bot_unique ((le_inf hcomm₁ hcomm₂).trans (critical_points_disjoint h hV hH i).le)
  have hcent : i.conjugate D.UH ≤ centralizer (D.V : Set G) := by
    rw [←hC]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (le_conjugateSpanBy _ _))
  exact i.noncentral ((commutator_eq_bot_iff_le_centralizer.mpr hcent).le.trans bot_le)

include h in
/-- The same endpoint reversal exchanges the two indices, proving the
choice in F.9.16(4) without assuming an inequality witness. -/
theorem critical_index_choice
    (hn : ∀ i : h.CriticalEndpoint, ¬ i.conjugate D.UH ≤ D.QH)
    (hb : 3 ≤ h.b) (i : h.CriticalEndpoint) :
    ∃ j : h.CriticalEndpoint,
      (j.conjugate D.QH).relIndex D.UH ≤ D.QH.relIndex (j.conjugate D.UH) := by
  by_cases hi : (i.conjugate D.QH).relIndex D.UH ≤ D.QH.relIndex (i.conjugate D.UH)
  · exact ⟨i,hi⟩
  obtain ⟨j,hj⟩ := i.reverse_labels hb (hn i)
  have hU := hj D.UH (le_normalizer_conjugateSpanBy _ _)
  have hQ := hj D.QH H_normalizes_QH
  have he₁ := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    D.QH (i.conjugate D.UH)
    (MulAut.conj j.representative).injective
  have he₂ := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (i.conjugate D.QH) D.UH
    (MulAut.conj j.representative).injective
  rw [hU] at he₁
  rw [hQ] at he₂
  exact ⟨j,he₁.trans_le ((le_of_not_ge hi).trans_eq he₂.symm)⟩


open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base)

include h in
/-- F.9.13(2) in the actual ambient group, with its H-conjugating element. -/
theorem critical_edge_core (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    ∃ t : D.H, i.conjugate D.UH ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2).conjBy (t : G) := by
  obtain ⟨w,hwt,hw,hc⟩ := i.edge_core hb
  obtain ⟨k,hkt,hkw⟩ := incident_common_translate (family (D := D)) hw.2
  change k • base (family (D := D)) true = base (family (D := D)) true at hkt
  rw [hwt] at hkw
  have hk : k ∈ family (D := D) true := by
    rw [←stabilizer_base (family (D := D)) true]
    exact hkt
  have hnorm : (family (D := D) true).map (MulAut.conj k).toMonoidHom =
      family (D := D) true :=
    mem_normalizer_iff_map_conj_eq.mp ((family (D := D) true).le_normalizer hk)
  refine ⟨⟨(k : G),hk⟩,(map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans ?_⟩
  have he : (stabilizer (family (D := D)) (base (family (D := D)) true) ⊓
      stabilizer (family (D := D)) w).map (D.LT ⊔ D.H).subtype =
      (D.L₁ ⊔ (D.T : Subgroup G)).conjBy (k : G) := by
    rw [←hkw,stabilizer_translate,show stabilizer (family (D := D)) (base (family (D := D)) true) =
        family (D := D) true from stabilizer_base (family (D := D)) true,
      show stabilizer (family (D := D)) (base (family (D := D)) false) =
        family (D := D) false from stabilizer_base (family (D := D)) false,←hnorm,
      ←map_inf _ _ _ (MulAut.conj k).injective,conjugate_map_ambient,
      map_inf _ _ _ (D.LT ⊔ D.H).subtype_injective]
    change ((D.H.subgroupOf (D.LT ⊔ D.H)).map (D.LT ⊔ D.H).subtype ⊓
      (D.LT.subgroupOf (D.LT ⊔ D.H)).map (D.LT ⊔ D.H).subtype).map _ = _
    rw [map_subgroupOf_eq_of_le le_sup_right,map_subgroupOf_eq_of_le le_sup_left,
      inf_comm,h.LT_inf_H_eq]
    rfl
  rw [he] at hc
  change i.conjugate D.VH ≤ ((D.L₁ ⊔ (D.T : Subgroup G)).map
    (MulAut.conj (k : G)).toMonoidHom).pCoreIn 2 at hc
  rw [AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (MulAut.conj (k : G)).injective] at hc
  exact hc

omit [Finite G] in
private theorem image_conjugate (H A : Subgroup G) (hA : A ≤ H)
    (π : H →* Product) (t : H) :
    ((A.conjBy (t : G)).subgroupOf H).map π =
      ((A.subgroupOf H).map π).conjBy (π t) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,ha,he⟩ := hx
    let aH : H := ⟨a,hA ha⟩
    have hx' : x = t * aH * t⁻¹ := Subtype.ext he.symm
    rw [hx',map_mul,map_mul,map_inv]
    exact ⟨π aH,mem_map_of_mem π ha,rfl⟩
  · rintro ⟨z,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨t*a*t⁻¹,?_,?_⟩
    · exact ⟨a,ha,rfl⟩
    · simp only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]

/-- The component factor in the specified product marking. -/
def quinticComponent : Subgroup Product :=
  (alternatingGroup (Fin 5)).prod ⊥

instance quinticComponent_normal : quinticComponent.Normal := by
  unfold quinticComponent
  infer_instance

include h in
/-- Transport the marked edge-core bounds to every critical module. -/
theorem critical_image_bounds
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hRcard : Nat.card ((((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2).subgroupOf D.H).map
      (productMap e)) ≤ 4)
    (hRK : (((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2).subgroupOf D.H).map
      (productMap e) ≤ quinticComponent)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    D.QH.relIndex (i.conjugate D.UH) ≤ 4 ∧
      ((i.conjugate D.UH).subgroupOf D.H).map (productMap e) ≤ quinticComponent := by
  obtain ⟨t,ht⟩ := critical_edge_core h i hb
  let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
  have hRH : R ≤ D.H := (pCoreIn_le 2 _).trans h.local_le
  have hm := map_mono (f := productMap e) (comap_mono (f := D.H.subtype) ht)
  change ((i.conjugate D.UH).subgroupOf D.H).map (productMap e) ≤
    ((R.conjBy (t : G)).subgroupOf D.H).map (productMap e) at hm
  rw [image_conjugate D.H R hRH (productMap e) t] at hm
  have hcard := (card_le_of_le hm).trans
    ((card_map_of_injective (MulAut.conj (productMap e t)).injective).le.trans hRcard)
  have hk : (productMap e).ker = pCore 2 D.H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 D.H) x) = 1 ↔ x ∈ pCore 2 D.H
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have huH : i.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (i.large_le hb)
  have he := relIndex_map_map_of_injective (f := D.H.subtype)
    (pCore 2 D.H) ((i.conjugate D.UH).subgroupOf D.H) D.H.subtype_injective
  rw [map_subgroupOf_eq_of_le huH] at he
  change D.QH.relIndex (i.conjugate D.UH) = _ at he
  rw [he,←hk,relIndex_ker]
  exact ⟨hcard,hm.trans ((map_mono hRK).trans_eq (Normal.map_conj_eq _ _))⟩



include h in
/-- Construct the critical endpoint, the same nontrivial A₅ actor, and both
filtration subgroups from the original F.9 geometry. -/
theorem marked_edge_contradiction
    (hV : D.V ≤ D.QH) (hH : D.H = D.Gz)
    (hC : centralizer (D.Vplus : Set G) = centralizer (D.V : Set G))
    (hc : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e))
    (hRcard : Nat.card ((((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2).subgroupOf D.H).map
      (productMap e)) ≤ 4)
    (hRK : (((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2).subgroupOf D.H).map
      (productMap e) ≤ quinticComponent) : False := by
  classical
  let := h.UH_elementary_of_V_le_QH hV
  have hb := (h.b_bounds_of_intersecting_conjugates_commute hV hc).1
  have hn (i : h.CriticalEndpoint) : ¬ i.conjugate D.UH ≤ D.QH :=
    critical_not_le_core h hV hH hC e hplace i hb
  obtain ⟨i,hi⟩ := critical_index_choice h hn hb
    (Classical.choice (h.criticalEndpoint_nonempty hV hc))
  obtain ⟨hbound,hcomponent⟩ := critical_image_bounds h e hRcard hRK i hb
  obtain ⟨b,hbU,hbQ⟩ := SetLike.not_le_iff_exists.mp (hn i)
  let bH : D.H := ⟨b,(i.large_le hb) ((map_mono
    (conjugateSpanBy_mono h.plus_le le_rfl)) hbU)⟩
  have hbK := hcomponent (mem_map_of_mem (productMap e) (show bH ∈
    (i.conjugate D.UH).subgroupOf D.H from hbU))
  let a : alternatingGroup (Fin 5) := ⟨(productMap e bH).1,hbK.1⟩
  have he : productMap e bH = (a.val,1) := Prod.ext rfl (mem_bot.mp hbK.2)
  have hp : (productMap e bH)^2 = 1 := by
    let : IsElementaryAbelian 2 (i.conjugate D.UH) := IsElementaryAbelian.map _
    have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (i.conjugate D.UH)) ⟨b,hbU⟩
    have hp' : bH^2 = 1 := Subtype.ext (congrArg (fun x : i.conjugate D.UH => (x : G)) hp)
    rw [←map_pow,hp',map_one]
  have hane : a ≠ 1 := by
    intro ha
    have hzero : productMap e bH = 1 := by rw [he,ha]; rfl
    have hq : bH ∈ pCore 2 D.H := (QuotientGroup.eq_one_iff bH).mp
      (e.injective (hzero.trans (map_one e).symm))
    exact hbQ ⟨bH,hq,rfl⟩
  have ha : orderOf a = 2 := orderOf_eq_prime
    (Subtype.ext (congrArg Prod.fst hp)) hane
  let B := D.UH ⊓ i.conjugate D.QH
  let A := i.conjugate D.V₁
  have hB : B.relIndex D.UH ≤ 4 := by
    rw [show B = D.UH ⊓ i.conjugate D.QH from rfl,inf_relIndex_left]
    exact hi.trans hbound
  have hA : Nat.card A ≤ 2 :=
    ((card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card).le
  have hcomm : ⁅B,zpowers (bH : G)⁆ ≤ A := by
    have hm := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      h.commutator_UH_QH_le_point
    rw [map_commutator,commutator_comm] at hm
    exact (commutator_mono inf_le_right (zpowers_le.mpr hbU)).trans hm
  exact f9_terminal_contradiction h hV e hplace B A inf_le_left hB hA bH a ha he hcomm

end CFSG.Quasithin.Chapter12.Section06.Terminal
