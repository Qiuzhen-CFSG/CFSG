module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.Kernel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Membership
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Fusion

/-!
# Excluding the xi*lambda cyclic kernel by crossing fusion

Suppose xi*lambda centralizes the supplied section. It centralizes beta,
so alpha fixes tau-prime*(xi*lambda)*tau-prime = mu-prime*xi*(tau*lambda).
Write y for the alpha image of mu-prime. The alpha relations place y in
the known local centralizer of mu and xi, and force the alpha image of
tau*lambda to be mu⁻¹*y⁻¹*mu-prime*xi*(tau*lambda).

Both images are involutions conjugate to mu. The local table proves that
one is conjugate to pi*xi, pi*lambda, or tau*lambda*xi. The three supplied
fusions put each of these in pi's class, contradicting pi--mu nonfusion.
This establishes the cyclic exclusion without adding the absent relation
that alpha centralizes tau*lambda. Crossing fusion remains an explicit input.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.235.
Conjugation is g⁻¹*x*g. All finite tables use kernel reduction in the actual
order-384 centralizer and seven explicit conjugating words.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
private instance : DecidableEq Coordinates.H := inferInstance

private def cyclicPartner (y : Coordinates.H) : Coordinates.H :=
  Coordinates.mu⁻¹ * y⁻¹ * Coordinates.mup * Coordinates.xi * coreTau 0

private def cyclicFusionMark : Fin 3 → Coordinates.H :=
  ![Coordinates.pi * Coordinates.xi, Coordinates.pi * Coordinates.lam,
    coreTau 0 * Coordinates.xi]

private def cyclicConjugator : Fin 7 → Coordinates.H :=
  ![1, Coordinates.lam, Coordinates.mup, Coordinates.mup * Coordinates.lam,
    Coordinates.mup * Coordinates.taup, Coordinates.tau * Coordinates.taup, Coordinates.taup]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem cyclic_fusion_table (y : Coordinates.H)
    (hm : y * Coordinates.mu = Coordinates.mu * y)
    (hx : y * Coordinates.xi = Coordinates.xi * y)
    (hy : y ^ 2 = 1) (hp : cyclicPartner y ^ 2 = 1) :
    ∃ i : Fin 3, ∃ j : Fin 7,
      y = (cyclicConjugator j)⁻¹ * cyclicFusionMark i * cyclicConjugator j ∨
      cyclicPartner y = (cyclicConjugator j)⁻¹ * cyclicFusionMark i * cyclicConjugator j := by
  obtain ⟨c, rfl⟩ := Coordinates.word_bijective.surjective y
  have table : ∀ c : Coordinates.Code,
      let y := Coordinates.word c
      y * Coordinates.mu = Coordinates.mu * y →
      y * Coordinates.xi = Coordinates.xi * y →
      y ^ 2 = 1 → cyclicPartner y ^ 2 = 1 →
      ∃ i : Fin 3, ∃ j : Fin 7,
        y = (cyclicConjugator j)⁻¹ * cyclicFusionMark i * cyclicConjugator j ∨
        cyclicPartner y = (cyclicConjugator j)⁻¹ * cyclicFusionMark i * cyclicConjugator j := by
    decide +kernel
  exact table c hm hx hy hp

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : AlternatingSixSection (centralizer ({D.a10NoncentralInvolution e} : Set G)))

private theorem cyclic_model_pi : D.a10ModelEmbedding e Coordinates.pi = pi D e := rfl
private theorem cyclic_model_mu : D.a10ModelEmbedding e Coordinates.mu = mu D e := rfl
private theorem cyclic_model_tau : D.a10ModelEmbedding e Coordinates.tau = tau D e := rfl
private theorem cyclic_model_taup : D.a10ModelEmbedding e Coordinates.taup = tau' D e := rfl
private theorem cyclic_model_lam : D.a10ModelEmbedding e Coordinates.lam = lam D e := rfl
private theorem cyclic_model_xi : D.a10ModelEmbedding e Coordinates.xi = xi D e := rfl

variable [Finite G]

private theorem cyclic_alpha_mup_image (a : AlphaRelations D e 0) :
    ∃ y : Coordinates.H, D.a10ModelEmbedding e y =
        (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e Coordinates.mup) ∧
      y * Coordinates.mu = Coordinates.mu * y ∧
      y * Coordinates.xi = Coordinates.xi * y := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  have hAp : A (f Coordinates.pi) = f (Coordinates.pi * Coordinates.xi) := by
    simpa only [A, MulAut.conj_apply, inv_inv, normalizedXi, Fin.val_zero,
      pow_zero, one_mul] using a.pi_alpha
  have hAm : A (f Coordinates.mu) = f (Coordinates.mu * Coordinates.xi) := by
    simpa only [A, MulAut.conj_apply, inv_inv, normalizedXi, Fin.val_zero,
      pow_zero, one_mul] using a.mu_alpha
  have hAx : A (f Coordinates.xi) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv, normalizedXi, Fin.val_zero,
      pow_zero, one_mul] using a.xi_alpha
  have hl : Commute Coordinates.mup Coordinates.pi ∧ Commute Coordinates.mup Coordinates.mu ∧
      Commute Coordinates.mup Coordinates.xi := by
    unfold Commute SemiconjBy
    decide +kernel
  have h₁ := (hl.1.map f).map A
  have h₂ := (hl.2.1.map f).map A
  have h₃ := (hl.2.2.map f).map A
  rw [hAp] at h₁
  rw [hAm] at h₂
  rw [hAx] at h₃
  have hlocal : (Coordinates.mu * Coordinates.xi) * Coordinates.mu = Coordinates.xi ∧
      (Coordinates.pi * Coordinates.xi) * Coordinates.xi = Coordinates.pi := by decide +kernel
  have hξ : Commute (A (f Coordinates.mup)) (f Coordinates.xi) := by
    simpa only [← map_mul, hlocal.1] using h₂.mul_right h₃
  have hπ : Commute (A (f Coordinates.mup)) (f Coordinates.pi) := by
    simpa only [← map_mul, hlocal.2] using h₁.mul_right hξ
  have hmem : A (f Coordinates.mup) ∈ f.range := by
    rw [D.a10ModelEmbedding_range]
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [f, Coordinates.pi, D.a10ModelEmbedding_central e] using hπ.eq)
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, hy, ?_, ?_⟩
  · apply D.a10ModelEmbedding_injective e
    change f (y * Coordinates.mu) = f (Coordinates.mu * y)
    rw [map_mul, map_mul, hy]
    exact h₃.eq
  · apply D.a10ModelEmbedding_injective e
    change f (y * Coordinates.xi) = f (Coordinates.xi * y)
    rw [map_mul, map_mul, hy]
    exact hξ.eq

/-- Crossing fusion excludes the cyclic kernel generated by xi*lambda.
The proof computes both images forced by beta centralization; it does not
assume that alpha commutes with tau*lambda. -/
public theorem xi_lam_not_mem_sectionCentralizer_of_crossingFusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (hcross : IsConj (pi D e) (D.a10ModelEmbedding e (coreTau 0 * Coordinates.xi))) :
    xi D e * lam D e ∉ sectionCentralizer D e s := by
  intro hk
  have hd := source_alpha_choice_zero D e hxi d a
  subst d
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  let t := tau' D e
  have ht2 : t * t = 1 := by
    simpa only [pow_two] using element_square D e 4 (by decide)
  have hti : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht2).symm
  have hc : Commute (xi D e * lam D e) (sectionBeta D e 0 a) :=
    (mem_centralizer_iff.mp hk.2 _ (sectionBeta_mem D e s 0 a)).symm
  have hc' := hc.map (MulAut.conj t)
  have hbeta : (MulAut.conj t) (sectionBeta D e 0 a) = a.alpha := by
    change t * (t * a.alpha * t) * t⁻¹ = a.alpha
    rw [hti]
    calc
      _ = (t * t) * a.alpha * (t * t) := by group
      _ = a.alpha := by rw [ht2, one_mul, mul_one]
  have hq : (MulAut.conj t) (xi D e * lam D e) =
      f (Coordinates.mup * Coordinates.xi * coreTau 0) := by
    have he : Coordinates.taup * (Coordinates.xi * Coordinates.lam) * Coordinates.taup =
        Coordinates.mup * Coordinates.xi * coreTau 0 := by decide +kernel
    change t * (xi D e * lam D e) * t⁻¹ = _
    rw [hti]
    simpa only [f, map_mul, cyclic_model_taup,
      cyclic_model_xi, cyclic_model_lam] using congrArg f he
  rw [hbeta, hq] at hc'
  have hfixed : A (f (Coordinates.mup * Coordinates.xi * coreTau 0)) =
      f (Coordinates.mup * Coordinates.xi * coreTau 0) := by
    simp only [A, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, hc'.eq, inv_mul_cancel_left]
  obtain ⟨y, hy, hym, hyx⟩ := cyclic_alpha_mup_image D e a
  change f y = A (f Coordinates.mup) at hy
  have hAx : A (f Coordinates.xi) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv, normalizedXi, Fin.val_zero,
      pow_zero, one_mul] using a.xi_alpha
  have hsplit : f y * f Coordinates.mu * A (f (coreTau 0)) =
      f (Coordinates.mup * Coordinates.xi * coreTau 0) := by
    simpa only [map_mul, hAx, ← hy] using hfixed
  have hpartner : A (f (coreTau 0)) = f (cyclicPartner y) := by
    calc
      _ = (f Coordinates.mu)⁻¹ * (f y)⁻¹ *
          (f y * f Coordinates.mu * A (f (coreTau 0))) := by group
      _ = (f Coordinates.mu)⁻¹ * (f y)⁻¹ *
          f (Coordinates.mup * Coordinates.xi * coreTau 0) := by rw [hsplit]
      _ = _ := by simp only [cyclicPartner, map_mul, map_inv, mul_assoc]
  have hy2 : y ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, hy, ← map_pow, ← map_pow]
    have he : Coordinates.mup ^ 2 = 1 := by decide +kernel
    simp only [he, map_one]
  have hp2 : cyclicPartner y ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, ← hpartner, ← map_pow, ← map_pow]
    have he : coreTau 0 ^ 2 = 1 := by decide +kernel
    simp only [he, map_one]
  have hmarks (i : Fin 3) : IsConj (pi D e) (f (cyclicFusionMark i)) := by
    fin_cases i
    · change IsConj (pi D e) (f (Coordinates.pi * Coordinates.xi))
      simpa only [map_mul, f, cyclic_model_pi, cyclic_model_xi] using
        pi_xi_fusion_of_source_alpha D e hxi 0 a
    · change IsConj (pi D e) (f (Coordinates.pi * Coordinates.lam))
      simpa only [map_mul, f, cyclic_model_pi, cyclic_model_lam] using hpiLam
    · exact hcross
  have hmu : IsConj (f y) (mu D e) := by
    have h₁ : IsConj (f Coordinates.mup) (f y) := isConj_iff.mpr ⟨a.alpha⁻¹, by
      simpa only [A, MulAut.conj_apply, inv_inv] using hy.symm⟩
    have h₂ : IsConj (f Coordinates.mup) (f Coordinates.mu) := by
      apply f.map_isConj
      exact isConj_iff.mpr ⟨Coordinates.rho⁻¹, by decide +kernel⟩
    exact h₁.symm.trans h₂
  have htmem : f (coreTau 0) ∈ s.ambientSubgroup := by
    simpa only [coreTau, normalizedLam, Fin.val_zero, pow_zero, one_mul, map_mul,
      f, cyclic_model_tau, cyclic_model_lam] using
      tau_lam_mem_section_of_pi_lam_fusion D e s hfusion hpiLam
  have htorder : orderOf (f (coreTau 0)) = 2 := by
    rw [orderOf_injective f (D.a10ModelEmbedding_injective e)]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hpmu : IsConj (f (cyclicPartner y)) (mu D e) := by
    have h₁ : IsConj (f (coreTau 0)) (f (cyclicPartner y)) :=
      isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [A, MulAut.conj_apply, inv_inv] using hpartner⟩
    exact h₁.symm.trans (section_involution_isConj_mu D e s _ htmem htorder)
  obtain ⟨i, j, hj⟩ := cyclic_fusion_table y hym hyx hy2 hp2
  have hconj : IsConj (pi D e)
      (f ((cyclicConjugator j)⁻¹ * cyclicFusionMark i * cyclicConjugator j)) := by
    apply (hmarks i).trans
    apply f.map_isConj
    exact isConj_iff.mpr ⟨(cyclicConjugator j)⁻¹, by rw [inv_inv]⟩
  apply hfusion
  have hmufusion : IsConj (pi D e) (mu D e) := by
    rcases hj with hj | hj
    · exact (hj ▸ hconj).trans hmu
    · exact (hj ▸ hconj).trans hpmu
  simpa only [pi_eq, mu_eq] using hmufusion

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
