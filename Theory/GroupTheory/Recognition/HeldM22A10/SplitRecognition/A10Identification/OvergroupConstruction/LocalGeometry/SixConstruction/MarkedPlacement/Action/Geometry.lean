module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Membership
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds

/-!
# The marked centralizer and the alpha actor in the supplied A₆

The three marked involutions give eight distinct elements of C_A(pi*mu).
The actual A₆ centralizer has order eight, so these are all its elements.
Conjugating alpha by tau-prime gives an element beta of A. Its action and
Held's pi--mu nonfusion exclude centralization of beta by xi.

A second useful exclusion is purely numerical: no element centralizing A
can be conjugate to pi, whose centralizer has order 384, since |A| = 360.
This allows the extension-kernel argument to avoid an additional nu actor.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, pp.234–235.
Conjugation in the source is g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : AlternatingSixSection (centralizer ({D.a10NoncentralInvolution e} : Set G)))

private theorem model_pi : D.a10ModelEmbedding e Coordinates.pi = pi D e := rfl

private theorem model_mu : D.a10ModelEmbedding e Coordinates.mu = mu D e := rfl

private theorem model_mup : D.a10ModelEmbedding e Coordinates.mup = mu' D e := rfl

private theorem model_tau : D.a10ModelEmbedding e Coordinates.tau = tau D e := rfl

private theorem model_taup : D.a10ModelEmbedding e Coordinates.taup = tau' D e := rfl

private theorem model_lam : D.a10ModelEmbedding e Coordinates.lam = lam D e := rfl

private theorem model_xi : D.a10ModelEmbedding e Coordinates.xi = xi D e := rfl

public theorem source_alpha_choice_zero [Finite G]
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d) :
    d = 0 := by
  fin_cases d
  · rfl
  · exfalso
    apply hxi
    have hp : IsConj (D.a10ModelEmbedding e Coordinates.pi)
        (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi (⟨1, by decide⟩ : Bit))) :=
      isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [inv_inv] using a.pi_alpha⟩
    have hl : Coordinates.pi * normalizedXi (⟨1, by decide⟩ : Bit) = Coordinates.xi := by decide +kernel
    simpa only [hl, model_pi, model_xi] using hp

private theorem local_word_injective : Function.Injective (coreWord 0 0) := by
  decide +kernel

private theorem local_word_commute : ∀ i,
    coreWord 0 0 i * corePi = corePi * coreWord 0 0 i := by
  decide +kernel

/-- The eight marked words exhaust the involution centralizer in the supplied A₆. -/
public theorem section_centralizer_words [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (y : G) (hy : y ∈ s.ambientSubgroup)
    (hc : Commute y (pi D e * mu D e)) :
    ∃ i : WordCode, y = D.a10ModelEmbedding e (coreWord 0 0 i) := by
  let f := D.a10ModelEmbedding e
  have hp : f corePi ∈ s.ambientSubgroup := by
    simpa only [f, corePi, map_mul, model_pi, model_mu] using pi_mu_mem_section D e s
  have ht : f (coreTau 0) ∈ s.ambientSubgroup := by
    simpa only [f, coreTau, normalizedLam, Fin.val_zero, pow_zero, one_mul, map_mul, model_tau, model_lam] using
      tau_lam_mem_section_of_pi_lam_fusion D e s hfusion hpiLam
  have hs : f (coreSwap 0) ∈ s.ambientSubgroup := by
    simpa only [f, coreSwap, normalizedXi, Fin.val_zero, pow_zero, one_mul, map_mul, model_mup, model_xi] using
      mu'_xi_mem_section_of_pi_xi_fusion D e s hfusion
        (pi_xi_fusion_of_source_alpha D e hxi d a)
  let p : s.ambientSubgroup := ⟨f corePi, hp⟩
  let j := s.ambientAlternatingEquiv
  let K : Subgroup G := s.ambientSubgroup ⊓ centralizer ({f corePi} : Set G)
  let F (x : K) : centralizer ({j p} : Set (alternatingGroup (Fin 6))) :=
    ⟨j ⟨x, x.property.1⟩, mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  have hF : Function.Injective F := by
    intro x y h
    have hh : (⟨x, x.property.1⟩ : s.ambientSubgroup) = ⟨y, y.property.1⟩ :=
      j.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun z : s.ambientSubgroup => (z : G)) hh)
  have hp2 : orderOf (j p) = 2 := by
    rw [j.orderOf_eq, Subgroup.orderOf_mk,
      orderOf_injective f (D.a10ModelEmbedding_injective e)]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hcardK : Nat.card K ≤ 8 := by
    have hc8 := AlternatingSix.ShadowLocal.inner_involution_fixed_card (j p) hp2
    rw [AlternatingSix.ShadowLocal.inner_fixed_eq_centralizer] at hc8
    exact (Nat.card_le_card_of_injective F hF).trans_eq hc8
  let W (i : WordCode) : K := ⟨f (coreWord 0 0 i), by
    constructor
    · simp only [coreWord, map_mul, map_pow]
      exact mul_mem (mul_mem (pow_mem hp _) (pow_mem ht _)) (pow_mem hs _)
    · exact mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg f (local_word_commute i))⟩
  have hW : Function.Injective W := by
    intro i k h
    have hh : f (coreWord 0 0 i) = f (coreWord 0 0 k) :=
      congrArg (fun z : K => (z : G)) h
    exact local_word_injective (D.a10ModelEmbedding_injective e hh)
  have hsurj := (hW.bijective_of_nat_card_le (by
    simpa [WordCode, Bit] using hcardK)).2
  obtain ⟨i, hi⟩ := hsurj ⟨y, hy, mem_centralizer_singleton_iff.mpr (by
    simpa only [f, corePi, map_mul, model_pi, model_mu] using hc.eq)⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

/-- The conjugate of alpha used in the final centralizer argument. -/
@[expose] public noncomputable def sectionBeta (d : Bit) (a : AlphaRelations D e d) : G :=
  tau' D e * a.alpha * tau' D e

private theorem tau'_square : tau' D e * tau' D e = 1 := by
  simpa only [pow_two] using element_square D e 4 (by decide)

private theorem tau'_corePi : tau' D e * (pi D e * mu D e) * tau' D e = mu D e := by
  have h : Coordinates.taup * corePi * Coordinates.taup = Coordinates.mu := by decide +kernel
  simpa only [corePi, map_mul, model_taup, model_pi, model_mu] using congrArg (D.a10ModelEmbedding e) h

private theorem tau'_mu : tau' D e * mu D e * tau' D e = pi D e * mu D e := by
  have h : Coordinates.taup * Coordinates.mu * Coordinates.taup = corePi := by decide +kernel
  simpa only [corePi, map_mul, model_taup, model_pi, model_mu] using congrArg (D.a10ModelEmbedding e) h

public theorem sectionBeta_mem (d : Bit) (a : AlphaRelations D e d) :
    sectionBeta D e d a ∈ s.ambientSubgroup := by
  let t := tau' D e
  have ht : t * t = 1 := tau'_square D e
  have hti : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  apply s.mem_ambientSubgroup_of_cube_eq_one
  · apply mem_centralizer_singleton_iff.mpr
    have hcomm := a.corePi_commute.eq
    simp only [corePi, map_mul, model_pi, model_mu] at hcomm
    rw [← tau'_mu D e] at hcomm
    have hh := congrArg (fun z => t * z * t) hcomm
    have htt (z : G) : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
    simpa only [sectionBeta, show tau' D e = t from rfl,
      mul_assoc, ht, mul_one, one_mul, htt, mu_eq] using hh
  · change (t * a.alpha * t) ^ 3 = 1
    calc
      _ = (t * a.alpha * t⁻¹) ^ 3 := by rw [hti]
      _ = 1 := by rw [conj_pow, a.cube, mul_one, mul_inv_cancel]

public theorem sectionBeta_corePi (d : Bit) (a : AlphaRelations D e d) :
    (sectionBeta D e d a)⁻¹ * (pi D e * mu D e) * sectionBeta D e d a =
      D.a10ModelEmbedding e (corePi * coreSwap d) := by
  let t := tau' D e
  have hti : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr (tau'_square D e)).symm
  calc
    _ = t * (a.alpha⁻¹ * (t * (pi D e * mu D e) * t) * a.alpha) * t := by
      change (t * a.alpha * t)⁻¹ * (pi D e * mu D e) * (t * a.alpha * t) = _
      simp only [mul_inv_rev, hti]
      group
    _ = t * (a.alpha⁻¹ * D.a10ModelEmbedding e Coordinates.mu * a.alpha) * t := by
      rw [show t * (pi D e * mu D e) * t = mu D e from tau'_corePi D e]
      rfl
    _ = t * D.a10ModelEmbedding e (Coordinates.mu * normalizedXi d) * t := by rw [a.mu_alpha]
    _ = _ := by
      have hl : ∀ d, Coordinates.taup * (Coordinates.mu * normalizedXi d) *
          Coordinates.taup = corePi * coreSwap d := by decide +kernel
      simpa only [t, map_mul, model_taup] using congrArg (D.a10ModelEmbedding e) (hl d)

/-- No pi-class element centralizes an actual A₆ of order 360. -/
public theorem section_centralizer_not_isConj_pi [Finite G] (x : G)
    (hx : x ∈ centralizer (s.ambientSubgroup : Set G)) : ¬ IsConj (pi D e) x := by
  intro hf
  have hle : s.ambientSubgroup ≤ centralizer ({x} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx y hy)
  have hd := card_dvd_of_le hle
  rw [Nat.card_congr s.ambientAlternatingEquiv.toEquiv,
    AlternatingSix.ShadowLocal.card_A6,
    NoncentralAnalysis.Fusion.centralizer_card_of_isConj D (by simpa only [pi_eq] using hf)] at hd
  norm_num at hd

/-- Centerlessness excludes any section element from its conjugation kernel. -/
public theorem section_centralizing_mem_eq_one (x : G) (hx : x ∈ s.ambientSubgroup)
    (hc : x ∈ centralizer (s.ambientSubgroup : Set G)) : x = 1 := by
  have hz : (⟨x, hx⟩ : s.ambientSubgroup) ∈ center s.ambientSubgroup := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)
  rw [s.ambientSubgroup_center_eq_bot] at hz
  exact congrArg (fun z : s.ambientSubgroup => (z : G)) (show (⟨x, hx⟩ : s.ambientSubgroup) = 1 from hz)

/-- Alpha sends (pi*mu)*xi to pi, for the xi choice in its source relations. -/
public theorem source_corePi_xi_isConj_pi (d : Bit) (a : AlphaRelations D e d) :
    IsConj (D.a10ModelEmbedding e (corePi * normalizedXi d)) (pi D e) := by
  refine isConj_iff.mpr ⟨a.alpha⁻¹, ?_⟩
  rw [inv_inv, map_mul]
  have hp : a.alpha⁻¹ * D.a10ModelEmbedding e corePi * a.alpha =
      D.a10ModelEmbedding e corePi := by
    rw [mul_assoc, ← a.corePi_commute.eq, inv_mul_cancel_left]
  calc
    _ = (a.alpha⁻¹ * D.a10ModelEmbedding e corePi * a.alpha) *
        (a.alpha⁻¹ * D.a10ModelEmbedding e (normalizedXi d) * a.alpha) := by group
    _ = D.a10ModelEmbedding e corePi * D.a10ModelEmbedding e Coordinates.mu := by
      rw [hp, a.xi_alpha]
    _ = pi D e := by
      rw [← map_mul]
      have hl : corePi * Coordinates.mu = Coordinates.pi := by decide +kernel
      rw [hl, model_pi]

private theorem conj_eq_of_commute {a b : G} (h : Commute a b) : b⁻¹ * a * b = a := by
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

/-- This is Held's alpha contradiction, independent of a quotient-core construction. -/
public theorem source_xi_not_commute_sectionBeta [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (d : Bit) (a : AlphaRelations D e d) :
    ¬ Commute (D.a10ModelEmbedding e (normalizedXi d)) (sectionBeta D e d a) := by
  intro h
  let f := D.a10ModelEmbedding e
  let x := f (normalizedXi d)
  let m := f Coordinates.mup
  let t := f Coordinates.taup
  have ht : t * t = 1 := tau'_square D e
  have htx : t * x * t = m * x := by
    have hl : ∀ d, Coordinates.taup * normalizedXi d * Coordinates.taup =
        Coordinates.mup * normalizedXi d := by decide +kernel
    simpa only [t, x, m, ← map_mul] using congrArg f (hl d)
  have hc : Commute (m * x) a.alpha := by
    have hc := congrArg (fun z => t * z * t) h.eq
    change t * (x * (t * a.alpha * t)) * t =
      t * ((t * a.alpha * t) * x) * t at hc
    have he : (t * x * t) * a.alpha = a.alpha * (t * x * t) := by
      have htt (z : G) : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
      simpa only [mul_assoc, ht, mul_one, one_mul, htt] using hc
    rwa [htx] at he
  have hconj : a.alpha⁻¹ * m * a.alpha = m * x * f Coordinates.mu := by
    have hc' := conj_eq_of_commute hc
    have hsplit : a.alpha⁻¹ * (m * x) * a.alpha =
        (a.alpha⁻¹ * m * a.alpha) * (a.alpha⁻¹ * x * a.alpha) := by group
    rw [hsplit, show a.alpha⁻¹ * x * a.alpha = f Coordinates.mu from a.xi_alpha] at hc'
    have hm : f Coordinates.mu * f Coordinates.mu = 1 := by
      rw [← map_mul]
      have hl : Coordinates.mu * Coordinates.mu = 1 := by decide +kernel
      rw [hl, map_one]
    have hc'' := congrArg (fun z => z * f Coordinates.mu) hc'
    simpa only [mul_assoc, hm, mul_one] using hc''
  have hr : IsConj (f Coordinates.mup) (f Coordinates.mu) := by
    apply f.map_isConj
    exact isConj_iff.mpr ⟨Coordinates.rho⁻¹, by decide +kernel⟩
  have hma : IsConj (f Coordinates.mup) (f (Coordinates.mu * Coordinates.mup * normalizedXi d)) := by
    refine isConj_iff.mpr ⟨a.alpha⁻¹, ?_⟩
    rw [inv_inv]
    change a.alpha⁻¹ * m * a.alpha = _
    rw [hconj]
    have hl : ∀ d, Coordinates.mup * normalizedXi d * Coordinates.mu =
        Coordinates.mu * Coordinates.mup * normalizedXi d := by decide +kernel
    simpa only [m, x, ← map_mul] using congrArg f (hl d)
  have hp : IsConj (f Coordinates.pi) (f (Coordinates.pi * normalizedXi d)) :=
    isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [inv_inv] using a.pi_alpha⟩
  have hl : IsConj (f (Coordinates.pi * normalizedXi d))
      (f (Coordinates.mu * Coordinates.mup * normalizedXi d)) := by
    apply f.map_isConj
    refine isConj_iff.mpr ⟨(Coordinates.tau * Coordinates.taup)⁻¹, ?_⟩
    simp only [inv_inv]
    have hl : ∀ d, (Coordinates.tau * Coordinates.taup)⁻¹ *
        (Coordinates.pi * normalizedXi d) * (Coordinates.tau * Coordinates.taup) =
        Coordinates.mu * Coordinates.mup * normalizedXi d := by decide +kernel
    exact hl d
  apply hfusion
  have hf := (hr.symm.trans (hma.trans (hp.trans hl).symm)).symm
  simpa only [f, Coordinates.pi, LocalData.a10ModelEmbedding_central,
    Coordinates.mu, LocalData.a10NoncentralInvolution] using hf

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
