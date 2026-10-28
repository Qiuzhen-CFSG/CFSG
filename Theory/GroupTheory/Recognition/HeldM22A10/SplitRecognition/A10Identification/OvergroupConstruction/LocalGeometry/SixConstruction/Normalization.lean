module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.NormalizationObstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.XiSeparation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
import Mathlib.Tactic.FinCases

/-!
# Normalizing Held's xi without changing the noncentral involution

Held 2.7 proves that xi and pi*xi cannot both be conjugate to pi. The
binary choice in 2.8 is realized here by an actual automorphism of the
specified centralizer. It fixes every other mark, in particular mu, so
the original nonfusion hypothesis and the supplied normal A₆ section
transport to the chosen equivalence. The ambient A₆ subgroup is unchanged.
The final theorem combines this with the already proved lambda choice in
2.5; the xi transvection fixes lambda and preserves its normalization.

This is the normalization step only. It does not assert existence of the
order-three actors or the compatible six-point data of Sections 4--5.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.4--2.5 and 2.7--2.8, pp.226--229.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
namespace SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The central transvection changes only the last of the eight coordinates. -/
public theorem element_twist (i : Fin 8) (hi : i ≠ 7) :
    element D (e.trans xiTwistEquiv) i = element D e i := by
  change D.a10ModelEmbedding e (xiTwistEquiv.symm (modelElement i)) = _
  have h : xiTwistEquiv.symm (modelElement i) = modelElement i := by
    apply xiTwistEquiv.injective
    rw [MulEquiv.apply_symm_apply, xiTwistEquiv_generators, if_neg hi]
  rw [h]
  rfl

/-- Transport of an actual normal section along equality of its centralizing element. -/
public def transportSection {x y : G} (h : x = y)
    (s : NoncentralAnalysis.AlternatingSixSection (centralizer ({y} : Set G))) :
    NoncentralAnalysis.AlternatingSixSection (centralizer ({x} : Set G)) := by
  subst x
  exact s

public theorem transportSection_ambientSubgroup {x y : G} (h : x = y)
    (s : NoncentralAnalysis.AlternatingSixSection (centralizer ({y} : Set G))) :
    (transportSection h s).ambientSubgroup = s.ambientSubgroup := by
  subst x
  rfl

variable [Finite G] [IsSimpleGroup G]

/-- Held's proved separation chooses one of the two actual centralizer equivalences. -/
public theorem exists_xi_normalized_equiv_of_nonfusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ∃ e' : D.centralizer ≃* CentralizerModels.a10Centralizer,
      (e' = e ∨ e' = e.trans xiTwistEquiv) ∧
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10NoncentralInvolution e') ∧
      ¬ IsConj (pi D e') (xi D e') := by
  obtain ⟨d, hd⟩ :=
    NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.exists_normalizedXi_nonfusion D e
      (NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.xi_separation_of_nonfusion
        D e hfusion)
  fin_cases d
  · refine ⟨e, Or.inl rfl, rfl, hfusion, ?_⟩
    rw [pi_eq]
    change ¬ IsConj D.z (D.a10ModelEmbedding e NoncentralAnalysis.Coordinates.xi)
    simpa only [NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.normalizedXi,
      Fin.val_zero, pow_zero, one_mul] using hd
  · refine ⟨e.trans xiTwistEquiv, Or.inr rfl, mu_twist D e, ?_, ?_⟩
    · simpa only [← mu_eq, mu_twist] using hfusion
    · rw [pi_eq, xi_twist]
      change ¬ IsConj D.z (D.a10ModelEmbedding e NoncentralAnalysis.Coordinates.pi *
        D.a10ModelEmbedding e NoncentralAnalysis.Coordinates.xi)
      simpa only [NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.normalizedXi,
        Fin.val_one, pow_one, map_mul] using hd

/-- Normalization preserves every original input, including the actual ambient A₆. -/
public theorem exists_xi_normalized_section
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    ∃ (e' : D.centralizer ≃* CentralizerModels.a10Centralizer)
      (s' : NoncentralAnalysis.AlternatingSixSection
        (centralizer ({D.a10NoncentralInvolution e'} : Set G))),
      (e' = e ∨ e' = e.trans xiTwistEquiv) ∧
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10NoncentralInvolution e') ∧
      ¬ IsConj (pi D e') (xi D e') ∧
      s'.ambientSubgroup = s.ambientSubgroup := by
  obtain ⟨e', he', hm, hf, hx⟩ := exists_xi_normalized_equiv_of_nonfusion D e hfusion
  exact ⟨e', transportSection hm s, he', hm, hf, hx, transportSection_ambientSubgroup hm s⟩

/-- Perform both source choices, in 2.5 and 2.8, preserving the supplied section.
The xi transvection fixes lambda, so it preserves the first normalization. -/
public theorem exists_source_normalized_section
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    ∃ (e' : D.centralizer ≃* CentralizerModels.a10Centralizer)
      (s' : NoncentralAnalysis.AlternatingSixSection
        (centralizer ({D.a10NoncentralInvolution e'} : Set G))),
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10NoncentralInvolution e') ∧
      ¬ IsConj (pi D e') (lam D e') ∧
      ¬ IsConj (pi D e') (xi D e') ∧
      s'.ambientSubgroup = s.ambientSubgroup := by
  obtain ⟨e₀, hm₀, hl⟩ := NoncentralAnalysis.Fusion.exists_normalized_equiv_of_simple D e
  have hf₀ : ¬ IsConj D.z (D.a10NoncentralInvolution e₀) := by rwa [hm₀]
  obtain ⟨e', s', he', hm, hf, hx, hA⟩ :=
    exists_xi_normalized_section D e₀ hf₀ (transportSection hm₀ s)
  refine ⟨e', s', hm.trans hm₀, hf, ?_, hx,
    hA.trans (transportSection_ambientSubgroup hm₀ s)⟩
  have hl₀ : ¬ IsConj D.z (lam D e₀) := hl
  rw [pi_eq]
  rcases he' with rfl | rfl
  · exact hl₀
  · simpa only [lam, element_twist D e₀ 6 (by decide)] using hl₀

end SixConstruction
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
