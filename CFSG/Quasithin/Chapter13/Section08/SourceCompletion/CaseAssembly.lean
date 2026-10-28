module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations

/-!
# The two terminal cases on the original Section 13.8 pair

When a critical denominator is full, the preceding 13.8.33 module argument
must supply abelianness of U_L and the compatible maps in its two actual
chief filtrations. The source two-core and central-line containments are
proved here; the checked cubic invariant then contradicts those maps.

When both denominators are proper, 13.8.34 supplies the transported line
and the two ranks. Only then is the point-normalizer model requested, on
that same pair and line. Relative normality and the strict normal extension
give the final contradiction. No comparison of denominator indices, rank,
line containment, or preselected critical pair is an additional premise.

This is a conditional assembly. Its model maps, normal component supplement,
and the earlier ambient inputs still require their source producers. It is
not an unconditional proof of 13.8.1.
Source: Aschbacher--Smith, 13.8.8, 13.8.27, 13.8.33--34 and the final
paragraph of 13.8.1, printed pp.949,963,966--969.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseAssembly
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open A6Endgame.ActionAnalysis33 A6Endgame.ActionAnalysis33.ChiefModels
open Theory.SpecificGroups.SymmetricSix

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual maps required at the end of the case-one argument. The two
filtrations have the common top O₂(L₁T), and Q is the original O₂(LT).
No numerical chief-factor identity or contradiction is a field. -/
def CaseOneModels (T : Sylow 2 G) (L H V₃ V V₁ : Subgroup G) : Prop :=
  IsMulCommutative (Source.UL L H V₃) ∧
    ∃ A : Subgroup G, A ≤ sourceOne L T V₁ ∧ IsPGroup 3 A ∧
      ∃ f : A →* cubicActor, Function.Surjective f ∧
        Nonempty (FiltrationModels A ((L ⊔ (T : Subgroup G)).pCoreIn 2)
          L H V₃ V V₁ (sourceOne L T V₁ ⊔ (T : Subgroup G)) f)

/-- The p.968 comparison, with the original source two-core and line
containments discharged. Relative quotient maps retain their actual kernels. -/
theorem case_one_contradiction
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (models : CaseOneModels T L H V₃ V V₁) : False := by
  obtain ⟨hUL, A, hA, hA3, f, hf, ⟨models⟩⟩ := models
  let : IsMulCommutative (Source.UL L H V₃) := hUL
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have hULQ := Section07.span_UH_L_le_core (localNaturalSetup d) hF9
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hAH : A ≤ H := hA.trans (le_sup_left.trans hHz.1.2)
  have hline : V₁ ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (hAH.trans hF9.H_centralizes)
  exact filtration_contradiction A ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃ V V₁
    (sourceOne L T V₁) (T : Subgroup G) f hf hA3 (isPGroup_pCoreIn 2 _)
    models hULQ (hQT.trans hF9.T_le_H) hline

/-- Both alternatives of 13.8.8 are consumed on a constructed source pair.
The marked point-parabolic model is needed only after 13.8.34 has placed
the actual transported line inside U_H. The remaining assumptions are
explicit earlier source-stage conclusions, not a claim to 13.8.1. -/
theorem contradiction_of_source_cases
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (models : letI := d.uh_elementary hHz
      TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (case_one : ∀ c : CriticalPair L (T : Subgroup G) H V,
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) →
      CaseOneModels T L H V₃ V V₁)
    (point_models : ∀ c : CriticalPair L (T : Subgroup G) H V,
      Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ →
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ →
      c.Aone V₁ ≤ Source.UH H V₃ →
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
        Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer)) :
    False := by
  obtain ⟨c, _, _⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  by_cases hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃
  · by_cases hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃
    · obtain ⟨hline, hrank, hsmall⟩ := TerminalRanks.rank_and_lines_of_source d hHz hF9
        hgen hK hN hqs hcentral hcomm models c hDH hDγ
      exact Terminal.contradiction_of_point_normalizer d hHz hF9 c hH hgen hK hN hqs
        hcentral hcomm hDH hline.2 hrank hsmall (point_models c hDH hDγ hline.1)
    · exact case_one_contradiction d hHz hF9 (case_one c (.inr
        (eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hDγ)))
  · exact case_one_contradiction d hHz hF9 (case_one c (.inl
      (eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hDH)))

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseAssembly
