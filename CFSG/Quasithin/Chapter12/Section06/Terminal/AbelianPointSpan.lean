module
public import CFSG.Quasithin.Chapter12.Section06.Terminal.CriticalGeometry
import all CFSG.Quasithin.Chapter12.Section06.Terminal.CriticalGeometry

/-!
# The terminal contradiction below the full point centralizer

The earlier terminal proof used H=C_G(V1) to separate critical point lines.
Abelianness of the full point-centralizer span gives this separation for
any original H: an endpoint fixing V1 would put its module and V in the
same abelian span, contradicting its defining noncentrality.

The same quotient action and critical-endpoint reversal then construct
b, D_H and A1 and give displacement at most three and at least four.
The explicit product marking, cubic placement and edge-core bounds are
discharged by the original-source consumer in NaturalSource/AbelianProduct.
The internal import reuses the original private small-displacement proof
and supplies a public membership specification for its component factor;
no existing boundary is changed.

Source: Aschbacher--Smith F.9.13--17 and12.6.34, printed pp.322--324,838.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Terminal
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
variable (h : D.Hypothesis)

/-- Membership specification for the existing marked component factor. -/
theorem quinticComponent_eq_product :
    quinticComponent = (alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by rfl

include h in
/-- Abelianness at the full point centralizer separates the original critical
point lines even when H is a proper subgroup of that centralizer. -/
theorem critical_points_disjoint_of_point_span
    (hspan : IsMulCommutative (conjugateSpanBy D.V D.Gz))
    (i : h.CriticalEndpoint) : D.V₁ ⊓ i.conjugate D.V₁ = ⊥ := by
  apply inf_eq_bot_of_card_two_of_ne _ _ h.point_card
    ((card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card)
  intro he
  have hg : i.representative ∈ D.Gz := by
    rw [←h.normalizer_point_eq]
    exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  let W := conjugateSpanBy D.V D.Gz
  let : IsMulCommutative W := hspan
  have hUW : D.UH ≤ W := conjugateSpanBy_mono h.plus_le h.H_centralizes
  have hW : W.map (MulAut.conj i.representative).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy D.V D.Gz) hg)
  have hiW : i.conjugate D.UH ≤ W := (map_mono hUW).trans_eq hW
  apply i.noncentral
  exact ((commutator_mono hiW (le_conjugateSpanBy D.V D.Gz)).trans
    (commutator_self_eq_bot_iff.mpr inferInstance).le).trans bot_le

include h in
/-- The no-transvection result excludes U_gamma = D_gamma in F.9.16(1). -/
theorem critical_not_le_core_of_point_span (hV : D.V ≤ D.QH)
    (hspan : IsMulCommutative (conjugateSpanBy D.V D.Gz))
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
    bot_unique ((le_inf hcomm₁ hcomm₂).trans (critical_points_disjoint_of_point_span h hspan i).le)
  have hcent : i.conjugate D.UH ≤ centralizer (D.V : Set G) := by
    rw [←hC]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (le_conjugateSpanBy _ _))
  exact i.noncentral ((commutator_eq_bot_iff_le_centralizer.mpr hcent).le.trans bot_le)

include h in
/-- Construct the critical endpoint, the same nontrivial A₅ actor, and both
filtration subgroups from the original F.9 geometry. -/
theorem marked_edge_contradiction_of_point_span
    (hV : D.V ≤ D.QH)
    (hspan : IsMulCommutative (conjugateSpanBy D.V D.Gz))
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
    critical_not_le_core_of_point_span h hV hspan hC e hplace i hb
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
