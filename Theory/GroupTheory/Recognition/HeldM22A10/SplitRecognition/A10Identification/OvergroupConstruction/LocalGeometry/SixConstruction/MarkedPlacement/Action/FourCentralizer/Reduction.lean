module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.Kernel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Membership
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Fusion

/-!
# Reducing the order-four section centralizer to its two cyclic alternatives

The full kernel is already contained in the known order-384 centralizer.
Commuting with mu and the two marked section generators leaves sixteen
explicit words. Translation by mu reduces them to eight representatives.
The pi-class obstruction excludes three representatives, and beta excludes
xi. After excluding xi*lambda and pi*xi*lambda, only the desired four words
remain. The assumed kernel order four then forces lambda into the kernel.

The two cyclic exclusions are explicit hypotheses of this reduction;
this module does not assert the final source theorem.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.235.
All finite calculations use the actual centralizer coordinates and kernel
reduction. Conjugation in the source is g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

private instance : DecidableEq Coordinates.H := inferInstance

private def kernelRepresentative : Fin 8 → Coordinates.H :=
  ![1, Coordinates.lam, Coordinates.pi, Coordinates.xi,
    Coordinates.pi * Coordinates.lam, Coordinates.pi * Coordinates.xi,
    Coordinates.xi * Coordinates.lam, Coordinates.pi * Coordinates.xi * Coordinates.lam]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem kernel_table (x : Coordinates.H)
    (hm : x * Coordinates.mu = Coordinates.mu * x)
    (ht : x * coreTau 0 = coreTau 0 * x)
    (hs : x * coreSwap 0 = coreSwap 0 * x) :
    ∃ j : Bit, ∃ i : Fin 8, Coordinates.mu ^ j.val * x = kernelRepresentative i := by
  obtain ⟨c, rfl⟩ := Coordinates.word_bijective.surjective x
  have table : ∀ c : Coordinates.Code,
      let x := Coordinates.word c
      x * Coordinates.mu = Coordinates.mu * x →
      x * coreTau 0 = coreTau 0 * x →
      x * coreSwap 0 = coreSwap 0 * x →
      ∃ j : Bit, ∃ i : Fin 8, Coordinates.mu ^ j.val * x = kernelRepresentative i := by
    decide +kernel
  exact table c hm ht hs

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : AlternatingSixSection (centralizer ({D.a10NoncentralInvolution e} : Set G)))

private theorem model_pi : D.a10ModelEmbedding e Coordinates.pi = pi D e := rfl
private theorem model_mu : D.a10ModelEmbedding e Coordinates.mu = mu D e := rfl
private theorem model_mup : D.a10ModelEmbedding e Coordinates.mup = mu' D e := rfl
private theorem model_tau : D.a10ModelEmbedding e Coordinates.tau = tau D e := rfl
private theorem model_lam : D.a10ModelEmbedding e Coordinates.lam = lam D e := rfl
private theorem model_xi : D.a10ModelEmbedding e Coordinates.xi = xi D e := rfl

variable [Finite G]

private theorem kernel_representatives
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (x : G) (hx : x ∈ sectionCentralizer D e s) :
    ∃ j : Bit, ∃ i : Fin 8,
      (mu D e) ^ j.val * x = D.a10ModelEmbedding e (kernelRepresentative i) := by
  let f := D.a10ModelEmbedding e
  have hxH : x ∈ f.range := by
    rw [D.a10ModelEmbedding_range]
    exact sectionCentralizer_le_original D e s hx
  obtain ⟨y, rfl⟩ := hxH
  have hcomm (z : Coordinates.H) (hz : f z ∈ s.ambientSubgroup) : y * z = z * y := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using (mem_centralizer_iff.mp hx.2 _ hz).symm
  have hm : y * Coordinates.mu = Coordinates.mu * y := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, model_mu] using mem_centralizer_singleton_iff.mp hx.1
  have ht : y * coreTau 0 = coreTau 0 * y := by
    apply hcomm
    simpa only [f, coreTau, normalizedLam, Fin.val_zero, pow_zero, one_mul, map_mul, model_tau, model_lam] using
      tau_lam_mem_section_of_pi_lam_fusion D e s hfusion hpiLam
  have hs : y * coreSwap 0 = coreSwap 0 * y := by
    apply hcomm
    simpa only [f, coreSwap, normalizedXi, Fin.val_zero, pow_zero, one_mul, map_mul, model_mup, model_xi] using
      mu'_xi_mem_section_of_pi_xi_fusion D e s hfusion
        (pi_xi_fusion_of_source_alpha D e hxi d a)
  obtain ⟨j, i, hi⟩ := kernel_table y hm ht hs
  exact ⟨j, i, by simpa only [map_mul, map_pow, f, model_mu] using congrArg f hi⟩

/-- The known marks and alpha leave only the central four-group or two cyclic kernels. -/
public theorem sectionCentralizer_mem_four_of_cyclic_exclusions
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (hxl : xi D e * lam D e ∉ sectionCentralizer D e s)
    (hpxl : pi D e * xi D e * lam D e ∉ sectionCentralizer D e s)
    (x : G) (hx : x ∈ sectionCentralizer D e s) :
    x = 1 ∨ x = mu D e ∨ x = lam D e ∨ x = mu D e * lam D e := by
  let f := D.a10ModelEmbedding e
  obtain ⟨j, i, hi⟩ := kernel_representatives D e s hfusion hpiLam hxi d a x hx
  have hr : f (kernelRepresentative i) ∈ sectionCentralizer D e s :=
    hi ▸ mul_mem (pow_mem (mu_mem_sectionCentralizer D e s) _) hx
  have hbad (z : G) (hz : IsConj (pi D e) z) : z ∉ sectionCentralizer D e s :=
    fun hc => section_centralizer_not_isConj_pi D e s z hc.2 hz
  have hp : pi D e ∉ sectionCentralizer D e s := hbad _ (IsConj.refl _)
  have hpl : pi D e * lam D e ∉ sectionCentralizer D e s := hbad _ hpiLam
  have hpx : pi D e * xi D e ∉ sectionCentralizer D e s :=
    hbad _ (pi_xi_fusion_of_source_alpha D e hxi d a)
  have hx' : xi D e ∉ sectionCentralizer D e s := by
    intro hc
    have hd := source_alpha_choice_zero D e hxi d a
    subst d
    apply source_xi_not_commute_sectionBeta D e hfusion 0 a
    have hh := (mem_centralizer_iff.mp hc.2 _ (sectionBeta_mem D e s 0 a)).symm
    change _ * _ = _ * _
    simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, model_xi] using hh
  have hsmall : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      apply hp
      change f (Coordinates.pi) ∈ sectionCentralizer D e s at hr
      simpa only [f, model_pi] using hr
    · exfalso
      apply hx'
      change f (Coordinates.xi) ∈ sectionCentralizer D e s at hr
      simpa only [f, model_xi] using hr
    · exfalso
      apply hpl
      change f (Coordinates.pi * Coordinates.lam) ∈ sectionCentralizer D e s at hr
      simpa only [f, map_mul, model_pi, model_lam] using hr
    · exfalso
      apply hpx
      change f (Coordinates.pi * Coordinates.xi) ∈ sectionCentralizer D e s at hr
      simpa only [f, map_mul, model_pi, model_xi] using hr
    · exfalso
      apply hxl
      change f (Coordinates.xi * Coordinates.lam) ∈ sectionCentralizer D e s at hr
      simpa only [f, map_mul, model_lam, model_xi] using hr
    · exfalso
      apply hpxl
      change f (Coordinates.pi * Coordinates.xi * Coordinates.lam) ∈ sectionCentralizer D e s at hr
      simpa only [f, map_mul, model_pi, model_lam, model_xi] using hr
  have hm2 : mu D e * mu D e = 1 := by
    simpa only [pow_two] using element_square D e 1 (by decide)
  rcases hsmall with rfl | rfl
  · change (mu D e) ^ j.val * x = f 1 at hi
    rw [map_one] at hi
    fin_cases j
    · exact Or.inl (by simpa only [Fin.val_zero, pow_zero, one_mul] using hi)
    · right; left
      have hh := congrArg (fun z => mu D e * z) hi
      simpa only [pow_one, ← mul_assoc, hm2, one_mul, mul_one] using hh
  · change (mu D e) ^ j.val * x = lam D e at hi
    fin_cases j
    · exact Or.inr (Or.inr (Or.inl (by simpa only [Fin.val_zero, pow_zero, one_mul] using hi)))
    · right; right; right
      have hh := congrArg (fun z => mu D e * z) hi
      simpa only [pow_one, ← mul_assoc, hm2, one_mul] using hh

public theorem section_centralizes_four_of_cyclic_exclusions
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (hcard : Nat.card (sectionCentralizer D e s) = 4)
    (hxl : xi D e * lam D e ∉ sectionCentralizer D e s)
    (hpxl : pi D e * xi D e * lam D e ∉ sectionCentralizer D e s) :
    s.ambientSubgroup ≤ centralizer ({mu D e, lam D e} : Set G) := by
  have hl : lam D e ∈ sectionCentralizer D e s := by
    classical
    by_contra hn
    have hcases (x : sectionCentralizer D e s) : (x : G) = 1 ∨ (x : G) = mu D e := by
      rcases sectionCentralizer_mem_four_of_cyclic_exclusions D e s hfusion hpiLam hxi d a
        hxl hpxl x x.property with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hn (h ▸ x.property)).elim
      · exfalso
        apply hn
        have hh := mul_mem (mu_mem_sectionCentralizer D e s) x.property
        rw [h, ← mul_assoc] at hh
        have hm2 : mu D e * mu D e = 1 := by
          simpa only [pow_two] using element_square D e 1 (by decide)
        simpa only [hm2, one_mul] using hh
    let f (x : sectionCentralizer D e s) : Fin 2 := if (x : G) = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      rcases hcases x with hx | hx <;> rcases hcases y with hy | hy
      · exact hx.trans hy.symm
      · exfalso
        have hn : ¬ mu D e = 1 := element_ne_one D e 1
        simp only [f, hx, hy, if_neg hn] at h
        exact (by decide : (0 : Fin 2) ≠ 1) h
      · exfalso
        have hn : ¬ mu D e = 1 := element_ne_one D e 1
        simp only [f, hx, hy, if_neg hn] at h
        exact (by decide : (1 : Fin 2) ≠ 0) h
      · exact hx.trans hy.symm
    have hc := Nat.card_le_card_of_injective f hf
    rw [hcard, Nat.card_fin] at hc
    omega
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact (mem_centralizer_singleton_iff.mp (s.ambientSubgroup_le hx)).symm
  · have he : y = lam D e := Set.mem_singleton_iff.mp hy
    subst y
    exact (mem_centralizer_iff.mp hl.2 _ hx).symm

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
