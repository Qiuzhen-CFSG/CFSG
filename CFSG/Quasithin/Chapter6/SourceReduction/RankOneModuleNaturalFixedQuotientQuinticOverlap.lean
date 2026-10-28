module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuintic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneSource

/-!
# Normality of the original quintic residual in the maximal overlap

An omega-centralizer maximal overgroup cannot contain L, because original
H-star centralization would place an outside H-star subgroup in M.
Consequently M∩M₁ preserves the literal Borel N_L(T∩L), hence its
characteristic quintic residual X. The same X lies in both maximal groups.
Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M M₁ V : Subgroup G} {n : ℕ}

/-- The actual X is contained in M∩M₁ and normalized by that whole overlap. -/
theorem original_hermitian_quintic_overlap
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    quinticResidual T L ≤ M ⊓ M₁ ∧
      M ⊓ M₁ ≤ normalizer (quinticResidual T L : Set G) := by
  let hi := h.reduced_enlargement.rankOneInput hout
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hLM₁ : ¬ L ≤ M₁ := by
    intro hle
    have he : M₁ = M := (hi.unique_local_join M₁ hM₁ (sup_le hle hTM₁)).trans
      h.maximal_eq_normalizer_L.symm
    obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
    have hH' := hH
    rw [h.maximal_eq_normalizer_L] at hH'
    exact hH.1.2 (((hi.hstar_centralizes_omega_of_hermitian hH' 2 (by decide) hm).trans
      hCM₁).trans_eq he)
  obtain ⟨_,_,_,_,_,_,hXC⟩ := original_hermitian_quintic_torus h hout hm
  refine ⟨le_inf (((map_subtype_le _).trans inf_le_left).trans h.L_le)
    ((le_sup_left.trans hXC).trans hCM₁),?_⟩
  rw [h.maximal_eq_normalizer_L]
  exact (intersection_normalizes_localBorel hi.linear hi.sylow_normalizes hTM₁ hLM₁).trans
    (quinticResidual_normalized T L)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
