module

public import CFSG.Quasithin.ChapterF.Section09.Setup
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The initial conclusions of F.9

The action kernel on U_H/V₁ is normal, so its containment in the seed
centralizer bounds it by the normal core in F.9.1(a). G.2.2 supplies the
opposite inclusion. The lifting condition (e) then turns centrality modulo
V₁ into the genuine centrality in F.9.3. Conjugate-span arguments give the
three elementary abelian criteria of F.9.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.2(1–3), F.9.3–4, printed p.318. The F.7 geometry in F.9.2(4) is separate.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

/-- F.9.2(1), central containment in the actual normalizer/point quotient. -/
theorem tilde_UH_central :
    D.tilde D.UH ≤ omegaOneAmbient
      ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype) :=
  h.g2_hypothesis.tilde_U_central.2

/-- F.9.2(2), with the Frattini subgroup embedded into G. -/
theorem frattini_UH_le_point : (frattini D.UH).map D.UH.subtype ≤ D.V₁ :=
  h.g2_hypothesis.frattini_U_le_point

theorem UH_le_QH : D.UH ≤ D.QH :=
  le_pCoreIn_of_normalizes h.g2_hypothesis.U_isPGroup h.UH_le_H
    (le_normalizer_conjugateSpanBy D.Vplus D.H)

theorem QH_le_T : D.QH ≤ (D.T : Subgroup G) :=
  (pCoreIn_le_sylow D.H (D.T.subtype h.T_le_H)).trans_eq
    (map_subgroupOf_eq_of_le h.T_le_H)

/-- The central containment expressed in ambient commutators. -/
theorem commutator_UH_QH_le_point : ⁅D.UH, D.QH⁆ ≤ D.V₁ := by
  let N := D.g2.G₁
  let : (D.V₁.subgroupOf N).Normal := D.g2.point_normal
  let q : N →* D.Tilde := QuotientGroup.mk' (D.V₁.subgroupOf N)
  have hHN : D.H ≤ N := h.g2_hypothesis.H_le
  apply commutator_le.mpr
  intro u hu x hx
  let uN : N := ⟨u, hHN (h.UH_le_H hu)⟩
  let xN : N := ⟨x, hHN (pCoreIn_le 2 D.H hx)⟩
  have huim : q uN ∈ D.tilde D.UH := mem_map_of_mem q hu
  have hxim : q xN ∈ D.tilde D.QH := mem_map_of_mem q hx
  obtain ⟨z, hz, he⟩ := omegaOneAmbient_le _ (h.tilde_UH_central huim)
  have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨q xN, hxim⟩)
  change q xN * z.val = z.val * q xN at hc
  change (z : D.Tilde) = q uN at he
  rw [he] at hc
  have hh : q ⁅uN, xN⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc.symm
  exact (QuotientGroup.eq_one_iff ⁅uN, xN⁆).mp hh

/-- The lower bound in the source kernel sandwich. -/
theorem QH_le_kernel_UH : D.QH ≤ h.kernel D.UH := by
  intro q hq
  exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨pCoreIn_le 2 D.H hq, fun u hu =>
    h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)⟩

/-- The centralizer of U_H/V₁ is relatively normal in H. -/
theorem kernel_UH_normal : ((h.kernel D.UH).subgroupOf D.H).Normal := by
  let := h.point_normal
  let := h.UH_normal
  change ((centralizerModulo ⊤ (D.UH.subgroupOf D.H) (D.V₁.subgroupOf D.H)).map
    D.H.subtype |>.comap D.H.subtype).Normal
  rw [comap_map_eq_self_of_injective D.H.subtype_injective]
  exact centralizerModulo_top_normal _ _

/-- F.9.2(3): no extra action-kernel equality is assumed. -/
theorem kernel_UH_eq_QH : h.kernel D.UH = D.QH := by
  apply le_antisymm _ h.QH_le_kernel_UH
  let := h.point_normal
  let := h.UH_normal
  let K := centralizerModulo (⊤ : Subgroup D.H) (D.UH.subgroupOf D.H)
    (D.V₁.subgroupOf D.H)
  let : K.Normal := centralizerModulo_top_normal _ _
  have hk : K ≤ (centralizerModulo (⊤ : Subgroup D.H) (D.Vplus.subgroupOf D.H)
      (D.V₁.subgroupOf D.H)).normalCore :=
    normal_le_normalCore.mpr (centralizerModulo_antitone
      (comap_mono (le_conjugateSpanBy D.Vplus D.H)))
  exact map_mono (hk.trans h.kernel_core)

/-- The intrinsic equality consumed by the literal H/V₁ action. -/
theorem centralizerModulo_UH_eq_pCore :
    let := h.point_normal
    centralizerModulo (⊤ : Subgroup D.H) (D.UH.subgroupOf D.H)
      (D.V₁.subgroupOf D.H) = pCore 2 D.H := by
  let := h.point_normal
  exact map_injective D.H.subtype_injective h.kernel_UH_eq_QH

/-- The full chain in F.9.2(3), including hypothesis (c). -/
theorem kernel_chain : D.QH = h.kernel D.UH ∧
    h.kernel D.UH ≤ h.kernel D.Vplus ∧
    h.kernel D.Vplus ≤ D.H ⊓ normalizer (D.V : Set G) := by
  let := h.point_normal
  refine ⟨h.kernel_UH_eq_QH.symm, ?_, ?_⟩
  · exact map_mono (centralizerModulo_antitone
      (comap_mono (le_conjugateSpanBy D.Vplus D.H)))
  · apply le_trans _ h.normalizer_control
    refine le_inf (map_subtype_le _) ?_
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_le.mpr
    intro v hv x hx
    exact h.point_lt.le ((h.mem_kernel_iff h.plus_le_H).mp hx |>.2 v hv)

/-- The remaining assertion of F.9.2(1), on the literal kernel quotient. -/
theorem kernel_quotient_core :
    let := h.kernel_UH_normal
    pCore 2 (D.H ⧸ (h.kernel D.UH).subgroupOf D.H) = ⊥ := by
  let := h.kernel_UH_normal
  have he : (h.kernel D.UH).subgroupOf D.H = pCore 2 D.H := by
    rw [h.kernel_UH_eq_QH]
    exact comap_map_eq_self_of_injective D.H.subtype_injective _
  let f := QuotientGroup.mk' ((h.kernel D.UH).subgroupOf D.H)
  have hk : f.ker = pCore 2 D.H := (QuotientGroup.ker_mk' _).trans he
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact pCore_isPGroup
  have hpre := f.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hp
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((h.kernel D.UH).subgroupOf D.H) x
  have hy : y ∈ f.ker := hk.symm ▸ (hpre.le hx)
  exact hy

omit [Finite G] h in
theorem H_normalizes_QH : D.H ≤ normalizer (D.QH : Set G) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨q, hq, rfl⟩
  exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹,
    (inferInstance : (pCore 2 D.H).Normal).conj_mem q hq ⟨g, hg⟩, rfl⟩

omit [Finite G] h in
private theorem conjugate_plus_le_UH (g : G) (hg : g ∈ D.H) :
    D.Vplus.map (MulAut.conj g).toMonoidHom ≤ D.UH := by
  rintro x ⟨a, ha, rfl⟩
  exact subset_closure ⟨g, hg, a, ha, rfl⟩

/-- The nontrivial implication in F.9.3 uses precisely source condition (e). -/
theorem V_centralizes_UH_of_le_QH (hV : D.V ≤ D.QH) :
    D.V ≤ D.H ⊓ centralizer (D.UH : Set G) := by
  refine le_inf h.V_le_H (le_centralizer_iff.mp ?_)
  apply (closure_le _).mpr
  rintro x ⟨g, hg, a, ha, rfl⟩
  let f := (MulAut.conj g).toMonoidHom
  have hQ : D.QH.map f = D.QH :=
    mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH (D := D) hg)
  have hVg : D.V.map f ≤ D.QH := (map_mono hV).trans_eq hQ
  have hc : ⁅D.V, D.QH⁆ ≤ D.V :=
    le_normalizer_iff_commutator_le_left.mp (h.QH_le_T.trans h.T_normalizes_V)
  have hcg : ⁅D.V.map f, D.QH⁆ ≤ D.V.map f := by
    have hm := map_mono (f := f) hc
    rwa [map_commutator, hQ] at hm
  have hinter : ⁅D.V, D.V.map f⁆ ≤ D.V ⊓ D.V.map f := by
    refine le_inf ((commutator_mono le_rfl hVg).trans hc) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl hV).trans hcg
  have hfirst : ⁅D.Vplus, D.V.map f⁆ ≤ D.V₁ :=
    (commutator_mono (le_conjugateSpanBy _ _) hVg).trans h.commutator_UH_QH_le_point
  have hsecond : ⁅D.Vplus.map f, D.V⁆ ≤ D.V₁ :=
    (commutator_mono (conjugate_plus_le_UH (D := D) g hg) hV).trans h.commutator_UH_QH_le_point
  exact commutator_eq_bot_iff_le_centralizer.mp
    (h.commutator_lifting g hg hinter hfirst hsecond).2 (mem_map_of_mem f ha)

/-- F.9.3: all three source conditions are equivalent. -/
theorem lemma_F_9_3 :
    (D.V ≤ D.QH ↔ D.V ≤ D.H ⊓ centralizer (D.UH : Set G)) ∧
    (D.V ≤ D.H ⊓ centralizer (D.UH : Set G) ↔ D.V ≤ h.kernel D.UH) := by
  have hCK : D.H ⊓ centralizer (D.UH : Set G) ≤ h.kernel D.UH := by
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1, fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact D.V₁.one_mem⟩
  constructor
  · exact ⟨h.V_centralizes_UH_of_le_QH, fun hv =>
      (hv.trans hCK).trans_eq h.kernel_UH_eq_QH⟩
  · exact ⟨fun hv => hv.trans hCK, fun hv =>
      h.V_centralizes_UH_of_le_QH (hv.trans_eq h.kernel_UH_eq_QH)⟩

/-- F.9.4(1). -/
theorem UH_elementary_of_V_le_QH (hv : D.V ≤ D.QH) : IsElementaryAbelian 2 D.UH := by
  let := h.elementary
  let : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
  let : IsMulCommutative (conjugateSpanBy D.Vplus D.H) := (conjugateSpanBy_commutative_iff _ _).mpr
    (h.plus_le.trans ((h.V_centralizes_UH_of_le_QH hv).trans inf_le_right))
  exact conjugateSpanBy_elementary_of_commutative D.Vplus D.H

private theorem UH_le_seed_centralizer [IsMulCommutative D.UH] :
    D.UH ≤ D.H ⊓ centralizer (D.Vplus : Set G) :=
  le_inf h.UH_le_H ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (Subgroup.centralizer_le (le_conjugateSpanBy D.Vplus D.H)))

private theorem seed_centralizer_le_normalizer :
    D.H ⊓ centralizer (D.Vplus : Set G) ≤ D.H ⊓ normalizer (D.V : Set G) :=
  (inf_le_inf_left D.H (Subgroup.centralizer_le_normalizer _)).trans h.normalizer_control

/-- F.9.4(2), retaining the quotient-commutator hypothesis and abelianness. -/
theorem V_le_QH_of_UH_abelian
    (hc : ⁅D.V, (D.H ⊓ centralizer (D.Vplus : Set G)) ⊓
      (D.H ⊓ normalizer (D.V : Set G))⁆ ≤ D.V₁)
    [IsMulCommutative D.UH] : D.V ≤ D.QH := by
  have hu := le_inf h.UH_le_seed_centralizer
    (h.UH_le_seed_centralizer.trans h.seed_centralizer_le_normalizer)
  have hcomm : ⁅D.V, D.UH⁆ ≤ D.V₁ := (commutator_mono le_rfl hu).trans hc
  rw [commutator_comm] at hcomm
  apply le_trans _ h.kernel_UH_eq_QH.le
  intro v hv
  exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨h.V_le_H hv, fun u hu =>
    hcomm (commutator_mem_commutator hu hv)⟩

private theorem seed_centralizer_eq
    (hc : (D.H ⊓ centralizer (D.Vplus : Set G)) ⊓
      (D.H ⊓ normalizer (D.V : Set G)) = D.H ⊓ centralizer (D.V : Set G)) :
    D.H ⊓ centralizer (D.Vplus : Set G) = D.H ⊓ centralizer (D.V : Set G) := by
  rwa [inf_eq_left.mpr h.seed_centralizer_le_normalizer] at hc

private theorem VH_elementary_of_UH_abelian
    (hc : (D.H ⊓ centralizer (D.Vplus : Set G)) ⊓
      (D.H ⊓ normalizer (D.V : Set G)) = D.H ⊓ centralizer (D.V : Set G))
    [IsMulCommutative D.UH] : IsElementaryAbelian 2 D.VH := by
  have hu : D.UH ≤ centralizer (D.V : Set G) := by
    have hu := h.UH_le_seed_centralizer
    rw [h.seed_centralizer_eq hc] at hu
    exact hu.trans inf_le_right
  have hvspan : D.VH ≤ centralizer (D.UH : Set G) :=
    conjugateSpanBy_le (le_centralizer_iff.mp hu)
      ((le_normalizer_conjugateSpanBy D.Vplus D.H).trans
        (normalizer_le_normalizer_centralizer _))
  have hvseed : D.VH ≤ D.H ⊓ centralizer (D.Vplus : Set G) :=
    le_inf h.VH_le_H (hvspan.trans
      (Subgroup.centralizer_le (le_conjugateSpanBy D.Vplus D.H)))
  rw [h.seed_centralizer_eq hc] at hvseed
  let : IsMulCommutative (conjugateSpanBy D.V D.H) := (conjugateSpanBy_commutative_iff _ _).mpr
    (le_centralizer_iff.mp (hvseed.trans inf_le_right))
  let := h.elementary
  exact conjugateSpanBy_elementary_of_commutative D.V D.H

/-- F.9.4(3), with all three conditions and its original conditional antecedent. -/
theorem lemma_F_9_4_three
    (hc : (D.H ⊓ centralizer (D.Vplus : Set G)) ⊓
      (D.H ⊓ normalizer (D.V : Set G)) = D.H ⊓ centralizer (D.V : Set G)) :
    (D.V ≤ D.QH ↔ IsElementaryAbelian 2 D.UH) ∧
    (IsElementaryAbelian 2 D.UH ↔ IsElementaryAbelian 2 D.VH) := by
  have hback (hv : IsElementaryAbelian 2 D.VH) : D.V ≤ D.QH := by
    let := hv
    exact (le_conjugateSpanBy D.V D.H).trans
      (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.VH)
        h.VH_le_H (le_normalizer_conjugateSpanBy D.V D.H))
  have hnext (hu : IsElementaryAbelian 2 D.UH) : IsElementaryAbelian 2 D.VH := by
    let := hu
    exact h.VH_elementary_of_UH_abelian hc
  exact ⟨⟨h.UH_elementary_of_V_le_QH, fun hu => hback (hnext hu)⟩,
    ⟨hnext, fun hv => h.UH_elementary_of_V_le_QH (hback hv)⟩⟩

/-- All normality, central-layer and commutator inputs of F.9.7, restricted
inside H. The final duality theorem can consume this without importing the
Section09 umbrella here. -/
theorem duality_inputs :
    (D.QH.subgroupOf D.H).Normal ∧ (D.UH.subgroupOf D.H).Normal ∧
    D.V₁.subgroupOf D.H ≤ D.QH.subgroupOf D.H ∧
    D.V₁.subgroupOf D.H ≤ center D.H ∧
    ⁅D.QH.subgroupOf D.H, D.UH.subgroupOf D.H⁆ ≤ D.V₁.subgroupOf D.H ∧
    Nat.card (D.V₁.subgroupOf D.H) = 2 := by
  refine ⟨?_, h.UH_normal, ?_, ?_, ?_, ?_⟩
  · have he : D.QH.subgroupOf D.H = pCore 2 D.H :=
      comap_map_eq_self_of_injective D.H.subtype_injective _
    rw [he]
    infer_instance
  · exact comap_mono ((h.point_lt.le.trans (le_conjugateSpanBy _ _)).trans h.UH_le_QH)
  · intro z hz
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext ((h.H_centralizes x.property) z hz).symm
  · apply commutator_le.mpr
    intro q hq u hu
    have hc := h.commutator_UH_QH_le_point
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hq hu)
  · exact (Nat.card_congr (subgroupOfEquivOfLe h.point_le_H).toEquiv).trans h.point_card

/-- The remaining F.9.7 input is exactly its stated elementary-abelian
assumption on U_H; restriction to H preserves it. -/
theorem duality_elementary (hu : IsElementaryAbelian 2 D.UH) :
    IsElementaryAbelian 2 (D.UH.subgroupOf D.H) := by
  let := hu
  exact IsElementaryAbelian.subgroupOf h.UH_le_H

end Hypothesis
end CFSG.Quasithin.ChapterF.Section09.Setup
