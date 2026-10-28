module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.DiagonalPair

/-!
# The original Suzuki centralizer conclusion from TypeRu

The preceding source proofs now construct H-control of s-fusion and the
original Sylow T_s. The diagonal fixed D10 supplies the actual non-core
witness needed by the residual recognition argument. Combine these with
J.2.3's original Sylow product, Suzuki two-group and Singer action to identify
the literal L_s with Sz(8), and recover the full centralizer product, involution
fusion and cubic normalizer action recorded by SuzukiSourceConclusion.

No marked-normalizer, fusion, small-model embedding or non-core premise remains.
The existing small-model-embedding interface is preserved by this separate route.

Source: Aschbacher–Smith J.2.9, printed p.438 (PDF p.449).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

open BenderSuzuki.MatrixGroups
open scoped Pointwise
public theorem suzuki_source : Nonempty c.SuzukiSourceConclusion := by
  let := c.S0_elementary_source
  obtain ⟨P,hP⟩ := c.Ts_sylow_source
  have h3 := (c.toSingerChoice.source_conclusions d c.sylowThree).three c.s c.s_mem c.s_ne_one
  obtain ⟨a, ha⟩ := h3.2.1
  change c.S0 × c.S1 ≃* c.Ts at a
  have hTsle : c.Ts ≤ c.Gs := inf_le_right
  let e0 : P ≃* c.Ts := (MulEquiv.subgroupCongr hP).trans (subgroupOfEquivOfLe hTsle)
  let e : P ≃* c.S0 × c.S1 := e0.trans a.symm
  have he (x : P) : ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G) := by
    have hh := ha (a.symm (e0 x)).1 (a.symm (e0 x)).2
    change (a (a.symm (e0 x)) : G) = _ at hh
    rw [a.apply_symm_apply] at hh
    exact hh
  have hS0 := c.S0_card_source
  have hTs : Nat.card c.Ts=256 := h3.2.2.2.1
  have hB := SourceCompletion.B_card c
  have hsuzuki := c.S1_suzuki_source
  have htrans := c.B7_transitive_source
  have hCL := c.local_centralizer_source
  have hH := c.H_eq_centralizer_z.symm
  have hHs := SourceCompletion.H_inf_Gs_eq_Ts c
  have hzV : c.z∈d.V := (d.center_eq.le c.z_mem_Z).1
  have hz1 : c.z≠1 := by intro h;have ho:=SourceCompletion.z_order c;simp [h] at ho
  have hsfusion := c.H_s_fusion_source
  have hVL := (c.V_le_S1 hsuzuki.2.1 htrans).trans c.S1_le_Ls
  have hzn := c.z_not_mem_twoCore_source
  obtain ⟨hd, _, hω, Q, hQ, hV, hC, hn, hti, hstrong⟩ :=
    c.residual_recognition_inputs P hP e he hsuzuki htrans hCL hH hHs hzV hz1
      hsfusion (IsConj.refl c.s) (c.Ls_le_Gs (hVL hzV)) (IsConj.refl c.z) hzn
  have hQcard : Nat.card Q = 64 := by
    rw [hQ, natCard_subgroupOf_eq c.S1 c.Ls c.S1_le_Ls]
    exact c.S1_card_of_local_product P hP e hS0 hTs
  obtain ⟨model⟩ := c.suzuki_of_residual_inputs Q hQ hQcard hVL hV hC hn
  obtain ⟨hc,prod,hprod⟩ := c.Gs_internalProduct_of_suzuki P hP e he model Q hQ hd
    (c.local_product_transfer_geometry P hP e he hsuzuki htrans).1
  have hGs := c.Gs_eq_S0_sup_Ls_of_local_product P hP e he
  have horbit := c.B_orbit_S0 hB
  have hfused : ∀ s0 ∈ c.S0, s0 ≠ 1 → IsConj c.s s0 := by
    intro s0 hs hs1
    obtain ⟨b,hb,hbEq⟩ := horbit s0 hs hs1
    exact isConj_iff.mpr ⟨b,hbEq⟩
  have hall (s0 : G) (hs : s0 ∈ c.S0) (hs1 : s0 ≠ 1) :=
    c.centralizer_S0_nonidentity hGs hc hfused hs hs1
  obtain ⟨hgen,hLN,hfactor⟩ := c.normalizer_S0_factorization hGs hc c.B_normalizes_S0 horbit
  have houter := c.B_outer_on_Ls model hB (c.B_normalizes_S0.trans hLN) hVL
  have hGsCard : Nat.card c.Gs = 116480 := by
    rw [← Nat.card_congr prod.toEquiv, Nat.card_prod, hS0,
      Nat.card_congr model.toEquiv, suzukiMatrixGroup_card 1 (by decide)]
    norm_num
  have hfree : ∀ b ∈ c.B, b ≠ 1 → ∀ s0 ∈ c.S0, s0 ≠ 1 → b*s0*b⁻¹ ≠ s0 := by
    intro b hb hb1 s0 hs hs1 hfix
    have hbGs : b ∈ c.Gs := by
      rw [← hall s0 hs hs1]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
    have hdis : Disjoint c.B c.Gs := disjoint_of_coprime_natCard (by
      rw [hB,hGsCard]; decide)
    exact hb1 (disjoint_def.mp hdis hb hbGs)
  let k := c.normalizerCubicProduct model hS0 hB hc hd hLN c.B_normalizes_S0
    (by rw [← hGs]; exact hgen) hfree houter
  refine ⟨{
    model := model
    sylow := Q
    sylow_eq := hQ
    sylow_card := hQcard
    omega_eq := hω
    centralizers := hC
    proper_normalizer := hn
    ti := hti
    strong_embedding := hstrong
    product := prod
    product_apply := hprod
    central := hc
    centralizer_eq := hGs
    centralizer_nonidentity := ?_
    normalizer_product := ?_
    normalizes_residual := hLN
    outer := houter
    involutions := c.z_class_intersection_Gs Q hQ hsuzuki htrans hzV hz1 hH hsfusion
    cubic := k
    cubic_E := rfl
    cubic_L := rfl
    cubic_B := rfl }⟩
  · intro s0 hs hs1
    exact (hall s0 hs hs1).trans hGs
  · ext n
    constructor
    · intro hn
      obtain ⟨g,hg,b,hb,heq⟩ := hfactor n hn
      exact Set.mem_mul.mpr ⟨g,hg,b,hb,heq.symm⟩
    · rintro ⟨g,hg,b,hb,rfl⟩
      rw [← hgen]
      exact (c.Gs ⊔ c.B).mul_mem ((show c.Gs ≤ c.Gs ⊔ c.B from le_sup_left) hg)
        ((show c.B ≤ c.Gs ⊔ c.B from le_sup_right) hb)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
