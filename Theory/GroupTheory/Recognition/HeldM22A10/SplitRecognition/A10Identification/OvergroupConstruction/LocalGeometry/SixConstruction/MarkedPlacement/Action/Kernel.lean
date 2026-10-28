module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.Geometry

/-!
# Faithful conjugation on the supplied A₆

Write X = A<mu-prime>. A centralizing element of X has a representative in
C_A(pi*mu), so the eight marked words leave only 1, pi*mu, xi and pi*mu*xi.
Centerlessness excludes pi*mu. Alpha excludes xi, and makes pi*mu*xi conjugate
to pi; the latter cannot centralize A by the centralizer order obstruction.
Thus X embeds in the actual automorphism group of the supplied A₆.

This proof uses neither a quotient-core reconstruction nor an additional nu
actor. The symmetric-group image and lambda centralization are separate steps.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, pp.234–235.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : AlternatingSixSection (centralizer ({D.a10NoncentralInvolution e} : Set G)))

/-- The actual ambient subgroup whose symmetric action is to be identified. -/
@[expose] public noncomputable def sectionExtension : Subgroup G :=
  s.ambientSubgroup ⊔ zpowers (mu' D e)

public theorem sectionExtension_le_normalizer :
    sectionExtension D e s ≤ normalizer (s.ambientSubgroup : Set G) :=
  sup_le s.ambientSubgroup.le_normalizer (zpowers_le.mpr (mu'_normalizes_section D e s))

/-- Conjugation, with the supplied A₆ as its carrier. -/
@[expose] public noncomputable def sectionAction : sectionExtension D e s →* MulAut s.ambientSubgroup :=
  s.ambientSubgroup.normalizerMonoidHom.comp (Subgroup.inclusion (sectionExtension_le_normalizer D e s))

public theorem sectionAction_apply (x : sectionExtension D e s) (y : s.ambientSubgroup) :
    (sectionAction D e s x y : G) = (x : G) * (y : G) * (x : G)⁻¹ := rfl

/-- The kernel of the full centralizer action, viewed in the ambient group. -/
@[expose] public noncomputable def sectionCentralizer : Subgroup G :=
  centralizer ({mu D e} : Set G) ⊓ centralizer (s.ambientSubgroup : Set G)

public theorem mu_mem_sectionCentralizer : mu D e ∈ sectionCentralizer D e s := by
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  change mu D e ∈ centralizer (s.ambientSubgroup : Set G)
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (s.ambientSubgroup_le hx)

/-- Centralizing mu and pi*mu places the full kernel in the known local model. -/
public theorem sectionCentralizer_le_original [Finite G] :
    sectionCentralizer D e s ≤ D.centralizer := by
  intro x hx
  have hm : Commute x (mu D e) := mem_centralizer_singleton_iff.mp hx.1
  have hp : Commute x (pi D e * mu D e) :=
    (mem_centralizer_iff.mp hx.2 _ (pi_mu_mem_section D e s)).symm
  have h := hp.mul_right hm.inv_right
  simp only [mul_inv_cancel_right, pi_eq] at h
  exact mem_centralizer_singleton_iff.mpr h.eq

/-- Normality is only relative to the extension. -/
public instance sectionExtension_section_normal :
    (s.ambientSubgroup.subgroupOf (sectionExtension D e s)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sectionExtension_le_normalizer D e s)

public theorem sectionExtension_cosets [Finite G] (x : G) (hx : x ∈ sectionExtension D e s) :
    ∃ y ∈ s.ambientSubgroup, ∃ j : Bit, x = y * (mu' D e) ^ j.val := by
  classical
  let X := sectionExtension D e s
  have htop : s.ambientSubgroup.subgroupOf X ⊔ (zpowers (mu' D e)).subgroupOf X = ⊤ := by
    rw [← subgroupOf_sup (A := s.ambientSubgroup) (A' := zpowers (mu' D e)) (B := X) le_sup_left le_sup_right]
    exact subgroupOf_self X
  have hx' : (⟨x, hx⟩ : X) ∈ s.ambientSubgroup.subgroupOf X ⊔
      (zpowers (mu' D e)).subgroupOf X := by rw [htop]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_left.mp hx'
  have hz' : (z : G) ∈ zpowers (mu' D e) := hz
  have hm2 : orderOf (mu' D e) = 2 := orderOf_eq_prime
    (element_square D e 2 (by decide)) (element_ne_one D e 2)
  rw [mem_zpowers_iff_mem_range_orderOf, hm2] at hz'
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hz'
  refine ⟨y, hy, ⟨j, Finset.mem_range.mp hj⟩, ?_⟩
  have h := congrArg (fun a : X => (a : G)) hyz
  simpa only [Subgroup.coe_mul, ← he] using h.symm

private theorem local_kernel_cases : ∀ i (j : Bit),
    (coreWord 0 0 i * Coordinates.mup ^ j.val) * coreTau 0 =
      coreTau 0 * (coreWord 0 0 i * Coordinates.mup ^ j.val) →
    (coreWord 0 0 i * Coordinates.mup ^ j.val) * coreSwap 0 =
      coreSwap 0 * (coreWord 0 0 i * Coordinates.mup ^ j.val) →
    coreWord 0 0 i * Coordinates.mup ^ j.val = 1 ∨
    coreWord 0 0 i * Coordinates.mup ^ j.val = corePi ∨
    coreWord 0 0 i * Coordinates.mup ^ j.val = normalizedXi 0 ∨
    coreWord 0 0 i * Coordinates.mup ^ j.val = corePi * normalizedXi 0 := by
  intro ⟨i, j, k⟩ l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

variable [Finite G]

/-- Every element of the extension centralizing A is the identity. -/
public theorem sectionExtension_centralizing_eq_one
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (x : G) (hx : x ∈ sectionExtension D e s)
    (hc : x ∈ centralizer (s.ambientSubgroup : Set G)) : x = 1 := by
  have hd := source_alpha_choice_zero D e hxi d a
  subst d
  let f := D.a10ModelEmbedding e
  have hp : f corePi = pi D e * mu D e := by
    rw [corePi, map_mul]
    rfl
  have ht : f (coreTau 0) = tau D e * lam D e := by
    rw [coreTau, normalizedLam]
    simp only [Fin.val_zero, pow_zero, one_mul, map_mul]
    rfl
  have hs : f (coreSwap 0) = mu' D e * xi D e := by
    rw [coreSwap, normalizedXi]
    simp only [Fin.val_zero, pow_zero, one_mul, map_mul]
    rfl
  have hpmem : f corePi ∈ s.ambientSubgroup := hp ▸ pi_mu_mem_section D e s
  have htmem : f (coreTau 0) ∈ s.ambientSubgroup := ht ▸
    tau_lam_mem_section_of_pi_lam_fusion D e s hfusion hpiLam
  have hsmem : f (coreSwap 0) ∈ s.ambientSubgroup := hs ▸
    mu'_xi_mem_section_of_pi_xi_fusion D e s hfusion (pi_xi_fusion_of_source_alpha D e hxi 0 a)
  have hcentral (z : G) (hz : z ∈ s.ambientSubgroup) : Commute x z :=
    (mem_centralizer_iff.mp hc z hz).symm
  obtain ⟨y, hy, j, rfl⟩ := sectionExtension_cosets D e s x hx
  have hz : Commute ((mu' D e) ^ j.val) (f corePi) := by
    have hl : ∀ k : Bit, Coordinates.mup ^ k.val * corePi =
        corePi * Coordinates.mup ^ k.val := by decide +kernel
    have hm : f Coordinates.mup = mu' D e := rfl
    exact show _ = _ from by simpa only [map_mul, map_pow, hm] using congrArg f (hl j)
  have hyc : Commute y (pi D e * mu D e) := by
    have h := (hcentral _ hpmem).mul_left hz.inv_left
    simpa only [mul_inv_cancel_right, hp] using h
  obtain ⟨i, rfl⟩ := section_centralizer_words D e s hfusion hpiLam hxi 0 a y hy hyc
  let w := coreWord 0 0 i * Coordinates.mup ^ j.val
  have hm : f Coordinates.mup = mu' D e := rfl
  have he : f w = f (coreWord 0 0 i) * (mu' D e) ^ j.val := by
    simp only [w, map_mul, map_pow, hm]
  have hw (z : G) (hz : z ∈ s.ambientSubgroup) : Commute (f w) z :=
    he.symm ▸ hcentral z hz
  have hwt : w * coreTau 0 = coreTau 0 * w := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using (hw _ htmem).eq
  have hws : w * coreSwap 0 = coreSwap 0 * w := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using (hw _ hsmem).eq
  have hwc : f w ∈ centralizer (s.ambientSubgroup : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    exact (hw z hz).symm.eq
  rw [← he]
  rcases local_kernel_cases i j hwt hws with h | h | h | h
  · rw [show w = 1 from h, map_one]
  · apply section_centralizing_mem_eq_one D e s (f w) _ hwc
    rwa [show w = corePi from h]
  · exact (source_xi_not_commute_sectionBeta D e hfusion 0 a
      (h ▸ hw _ (sectionBeta_mem D e s 0 a))).elim
  · exact (section_centralizer_not_isConj_pi D e s (f w) hwc
      (by simpa only [show w = corePi * normalizedXi 0 from h, f] using
        (source_corePi_xi_isConj_pi D e 0 a).symm)).elim

public theorem sectionAction_injective
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d) :
    Function.Injective (sectionAction D e s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hh : sectionAction D e s x = 1 := hx
  have hc : (x : G) ∈ centralizer (s.ambientSubgroup : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hy' := congrArg (fun z : s.ambientSubgroup => (z : G))
      (DFunLike.congr_fun hh ⟨y, hy⟩)
    rw [sectionAction_apply] at hy'
    exact (mul_inv_eq_iff_eq_mul.mp hy').symm
  exact Subtype.ext (sectionExtension_centralizing_eq_one D e s hfusion hpiLam hxi d a
    x x.property hc)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
