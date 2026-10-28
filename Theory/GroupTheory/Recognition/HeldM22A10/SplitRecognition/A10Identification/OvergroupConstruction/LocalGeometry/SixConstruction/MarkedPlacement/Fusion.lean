module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations

import Mathlib.Tactic.FinCases

/-!
# Recovering the supplied marking from earlier source choices

Held's S-fusion and alpha construction allow binary choices of lambda and xi.
The hypotheses that the supplied lambda and xi are not conjugate to pi rule
out the changed choice whenever pi is conjugate to pi times the chosen mark.
Thus the earlier constructions give the two precise fusions consumed by the
section-membership and action arguments, without changing the supplied e.

The two source constructions remain explicit inputs. These lemmas prove the
choice elimination, not the existence of S-fusion or of alpha.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 2.10–2.13 and 4.2, pp.229–235.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The supplied lambda normalization selects the original marking in the source fusion. -/
public theorem pi_lam_fusion_of_source_choice
    (hlam : ¬ IsConj (pi D e) (lam D e))
    (hsource : ∃ b : Bit,
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b))) :
    IsConj (pi D e) (pi D e * lam D e) := by
  have hl : lam D e = D.a10ModelEmbedding e Coordinates.lam := rfl
  obtain ⟨b, hb⟩ := hsource
  fin_cases b
  · simpa only [normalizedLam, Fin.val_zero, pow_zero, one_mul, map_mul,
      Coordinates.pi, LocalData.a10ModelEmbedding_central, pi_eq, hl] using hb
  · have hs : Coordinates.pi * (Coordinates.pi * Coordinates.lam) = Coordinates.lam := by decide +kernel
    simp only [normalizedLam, pow_one, hs] at hb
    exact (hlam (by simpa only [pi_eq, hl] using hb)).elim

/-- The source alpha relation and the supplied xi normalization determine pi--pi*xi fusion. -/
public theorem pi_xi_fusion_of_source_alpha
    (hxi : ¬ IsConj (pi D e) (xi D e))
    (d : Bit) (a : AlphaRelations D e d) :
    IsConj (pi D e) (pi D e * xi D e) := by
  have hx : xi D e = D.a10ModelEmbedding e Coordinates.xi := rfl
  have hp : IsConj (D.a10ModelEmbedding e Coordinates.pi)
      (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d)) :=
    isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [inv_inv] using a.pi_alpha⟩
  fin_cases d
  · simpa only [normalizedXi, Fin.val_zero, pow_zero, one_mul, map_mul,
      Coordinates.pi, LocalData.a10ModelEmbedding_central, pi_eq, hx] using hp
  · have hs : Coordinates.pi * (Coordinates.pi * Coordinates.xi) = Coordinates.xi := by decide +kernel
    simp only [normalizedXi, pow_one, hs] at hp
    exact (hxi (by simpa only [Coordinates.pi, LocalData.a10ModelEmbedding_central, pi_eq, hx]
      using hp)).elim

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
