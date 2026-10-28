module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates

/-!
# Conditional SL₃ cubic degree sieve and its absolute-model consumer

The original ambient cubic actor acts in the normalizer of the representation
inflated along the supplied central cover. The actual repeated tensor model
exists by absolute exhaustion and the exact Schur-field period theorem. The
inner and outer common-fixed-space estimates exclude its nonexceptional
patterns; the remaining two patterns have binary degree strictly below 8r.

The consumer applies `absolute_model_trichotomy` to the literal inflated
action, preserving its natural/twisted scalar-extension equivalences and dual
alternatives. Irreducibility, nontriviality and central kernel are derived from
the original source action and cover, not imposed on the inflated action.

The actor estimates and the projective automorphism-rank bound are still
explicit hypotheses. This module does not claim the unconditional K.3.2 sieve;
its owner retains their discharge and final assembly.

Source: Aschbacher–Smith, Chapter K standing hypotheses and K.3.2, printed
pp.451,454–456/PDF pp.462,465–467, citing GM04 Proposition 4.6/Table 7.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve

open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open ChapterB.QuasisimpleSource
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {B : BinaryField}

/-- Conditional strict degree bound from the original source hypotheses.
Only the two actor estimates and the intrinsic automorphism-rank calculation
remain to be discharged; no restricted cubic bound is used. -/
theorem finrank_lt_eight_mul_of_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) (C : LinearCover B 3 L)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hr : primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier))
      ≤ 2 * B.degree)
    (hinner : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      InnerWordEstimate B (inflated ρ C))
    (houter : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      OuterWordEstimate B (inflated ρ C)) :
    Module.finrank (ZMod 2) V < 8 * B.degree := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  obtain ⟨M⟩ := repeatedModel_nonempty B (inflated ρ C)
  obtain ⟨A, hA, hc, hArank, hd⟩ := source_actor ρ C h e hr
  exact M.finrank_lt_eight_mul (small_of_actor_estimates B (inflated ρ C)
    hinner houter (inflated_nontrivial ρ C h) M A hA hc hArank hd)

/-- The actual absolute-model consumer. The natural and half-field tensor
alternatives retain their coefficient embeddings, duals and intertwiners. -/
theorem absolute_models_of_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) (C : LinearCover B 3 L)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hr : primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier))
      ≤ 2 * B.degree)
    (hinner : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      InnerWordEstimate B (inflated ρ C))
    (houter : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      OuterWordEstimate B (inflated ρ C)) :
    let := h.finite_module
    let := inflated_irreducible ρ C h.irreducible
    0 < schurDegree (inflated ρ C) ∧
      ((schurDegree (inflated ρ C) = B.degree ∧
          Module.finrank (ZMod 2) V = 3 * B.degree ∧
          HasAbsoluteNaturalModel (inflated ρ C)) ∨
        (B.degree = 2 * schurDegree (inflated ρ C) ∧
          Module.finrank (ZMod 2) V = 9 * schurDegree (inflated ρ C) ∧
          HasAbsoluteTwistedModel (inflated ρ C) (schurDegree (inflated ρ C)))) := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  have hd := finrank_lt_eight_mul_of_estimates h C e hr hinner houter
  obtain ⟨hs, hnatural | htwisted | hlarge⟩ := absolute_model_trichotomy
    (inflated ρ C) (inflated_nontrivial ρ C h) B.degree B.degree_pos B.card_eq
  · exact ⟨hs, Or.inl hnatural⟩
  · exact ⟨hs, Or.inr htwisted⟩
  · exact False.elim ((not_le_of_gt hd) hlarge)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve
