module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.FourCentralizer.Reduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.FourCentralizer.Cyclic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.CrossFusion

/-!
# Completing the four-centralizer argument from the initial nu actor

The supplied initial Section 4.1 actor lies in A because it centralizes mu
and has cube one. Earlier crossing fusion forces it to commute with xi.
It already commutes with its chosen lambda. Consequently pi*xi*lambda
cannot centralize A: that would make nu centralize pi, contrary to its
specified action. The crossing-fusion calculation in `Cyclic` excludes
xi*lambda. `Reduction` and the kernel's order four then place lambda in
C_G(A).

Pi--pi*lambda fusion forces the seed's binary choice of lambda to be the
original marking. The initial seed is an explicit premise here. Its
construction from the original local hypotheses remains an upstream
obligation; neither the marked-section record nor lambda centralization
of A is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 4.1–4.2, pp.232–235.
Conjugation is g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : AlternatingSixSection (centralizer ({D.a10NoncentralInvolution e} : Set G)))

/-- The initial Section 4.1 actor eliminates the twisted cyclic representative.
Only its already-proved xi normalization, its lambda centralization and its
nontrivial action on pi are needed. -/
public theorem pi_xi_lam_not_mem_sectionCentralizer_of_nuSeed
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (a : AlphaRelations D e 0) (n : NuSeedRelations D e 0) :
    pi D e * xi D e * lam D e ∉ sectionCentralizer D e s := by
  let f := D.a10ModelEmbedding e
  have hx : f (normalizedXi 0) = xi D e := by
    simp only [normalizedXi, Fin.val_zero, pow_zero, one_mul]
    rfl
  have hl : f (normalizedLam 0) = lam D e := by
    simp only [normalizedLam, Fin.val_zero, pow_zero, one_mul]
    rfl
  have hp : f Coordinates.pi = pi D e := rfl
  have hcross := crossingFusion_of_seed a n hfusion
  have hsep : ¬ IsConj (f (normalizedXi 0)) (f (coreTau 0 * normalizedXi 0)) := by
    intro h
    exact hfusion ((hcross.trans h.symm).trans a.xi_isConj_mu)
  have hnxi : Commute n.nu (xi D e) := by
    have hfix : n.nu⁻¹ * xi D e * n.nu = xi D e := by
      rcases n.xi_conjugation (d := 0) with h | h
      · simp only [MulAut.conj_apply, inv_inv] at h
        change n.nu⁻¹ * f (normalizedXi 0) * n.nu = f (normalizedXi 0) at h
        rwa [hx] at h
      · exact (hsep (isConj_iff.mpr ⟨n.nu⁻¹, h⟩)).elim
    show n.nu * xi D e = xi D e * n.nu
    calc
      _ = n.nu * (n.nu⁻¹ * xi D e * n.nu) := by rw [hfix]
      _ = _ := by group
  have hnlam : Commute n.nu (lam D e) := hl ▸ n.lam_commute
  have hnmem : n.nu ∈ s.ambientSubgroup := by
    apply s.mem_ambientSubgroup_of_cube_eq_one
    · exact mem_centralizer_singleton_iff.mpr n.mu_commute.eq
    · exact n.cube
  intro hk
  have hkc : Commute (pi D e * xi D e * lam D e) n.nu :=
    (mem_centralizer_iff.mp hk.2 _ hnmem).symm
  have hxc : Commute (xi D e * lam D e) n.nu := hnxi.symm.mul_left hnlam.symm
  have hpc : Commute (pi D e) n.nu := by
    have hc := hkc.mul_left hxc.inv_left
    have he : pi D e * xi D e * lam D e * (xi D e * lam D e)⁻¹ = pi D e := by group
    exact he ▸ hc
  have hfix : n.nu⁻¹ * f Coordinates.pi * n.nu = f Coordinates.pi := by
    rw [hp, mul_assoc, hpc.eq, inv_mul_cancel_left]
  have he : f (Coordinates.pi * Coordinates.tau * normalizedLam 0) = f Coordinates.pi :=
    n.pi_nu.symm.trans hfix
  have hne : Coordinates.pi * Coordinates.tau * normalizedLam 0 ≠ Coordinates.pi := by
    decide +kernel
  exact hne (D.a10ModelEmbedding_injective e he)

/-- Conditional completion from the initial source actor. Its binary lambda
choice is forced to be the supplied one by pi--pi*lambda fusion. The source
crossing fusion eliminates the other cyclic representative. -/
public theorem section_centralizes_four_of_nuSeed
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : IsConj (pi D e) (pi D e * lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e)) (d : Bit) (a : AlphaRelations D e d)
    (hcard : Nat.card (sectionCentralizer D e s) = 4)
    (b : Bit) (n : NuSeedRelations D e b) :
    s.ambientSubgroup ≤ centralizer ({mu D e, lam D e} : Set G) := by
  have hd := source_alpha_choice_zero D e hxi d a
  subst d
  have hb : b = 0 := by
    fin_cases b
    · rfl
    · exfalso
      apply n.lambda_nonfusion hfusion
      have hp : D.a10ModelEmbedding e Coordinates.pi = pi D e := rfl
      have hl : D.a10ModelEmbedding e Coordinates.lam = lam D e := rfl
      simpa only [normalizedLam, pow_one, map_mul, hp, hl, pi_eq] using hpiLam
  subst b
  have hcross : IsConj (pi D e) (D.a10ModelEmbedding e (coreTau 0 * Coordinates.xi)) := by
    simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, pi_eq] using
      crossingFusion_of_seed a n hfusion
  exact section_centralizes_four_of_cyclic_exclusions D e s hfusion hpiLam hxi 0 a hcard
    (xi_lam_not_mem_sectionCentralizer_of_crossingFusion D e s hfusion hpiLam hxi 0 a hcross)
    (pi_xi_lam_not_mem_sectionCentralizer_of_nuSeed D e s hfusion a n)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
