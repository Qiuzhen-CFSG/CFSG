module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.LinearModels

/-!
# The original critical point and the terminal source contradiction

Whole-module coordinates identify the stabilizer of a nonfixed quotient
point with the concrete A₆ or S₆ point parabolic. Movement of the original
involution by O₂(H) lifts every quotient fixer to its actual centralizer.
The two ranks and both line containments are obtained from `TerminalRanks`
on the unchanged source critical pair. Relative normality of Uγ* < Vγ*
then contradicts the small normal-subgroup calculation in that parabolic.

The marked version uses one actor marking throughout. Its symmetric
module coordinates come from the existing marked natural/cover model.
No point-normalizer isomorphism is assumed. The ordinary surviving setup,
the strict denominators from 13.8.33, and movement and nonfixedness of the
critical point remain explicit source obligations. Consequently this is a
conditional application for the final assembly of 13.8.1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.8.34 and the final paragraph of 13.8.1, printed pp.968–969.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open A6Endgame A6Endgame.PointNormalizer TerminalRanks
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Construct the literal point-normalizer model and apply the source ranks. -/
theorem contradiction_of_linear_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (coords : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom))
    (hm : ∀ u ∈ c.Aone V₁, u ≠ 1 → ∃ n ∈ Source.QH H, n * u ≠ u * n)
    (hnf : letI := d.uh_elementary hHz
      ∀ u : Source.UH H V₃, (u : G) ∈ c.Aone V₁ → (u : G) ≠ 1 →
        ∃ g, a.action g (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ≠
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  obtain ⟨hline, hrank, hsmall⟩ := rank_and_lines_of_source d hHz hF9 hgen hK hN hqs
    hcentral hcomm models c hstrict hDstrict
  have hA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective, d.line_card]
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : c.Aone V₁)).mp hA
  have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  let v : Source.UH H V₃ := ⟨u, hline.1 u.property⟩
  have hv : (v : G) ∈ c.Aone V₁ := u.property
  have hv1 : (v : G) ≠ 1 := hu1
  have point_model :
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer) := by
    rcases coords with ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl (alternating_model_of_linear_coordinates a (c.Aone V₁) hA v hv hv1
        d.line_card hF9.commutator_UH_QH_le_point (hm v hv hv1) e he (hnf v hv hv1))
    · exact Or.inr (symmetric_model_of_linear_coordinates a (c.Aone V₁) hA v hv hv1
        d.line_card hF9.commutator_UH_QH_le_point (hm v hv hv1) e he (hnf v hv hv1))
  exact Terminal.contradiction_of_point_normalizer d hHz hF9 c hH hgen hK hN hqs
    hcentral hcomm hstrict hline.2 hrank hsmall point_model

/-- Use the same actor marking for the base edge and the terminal point.
The full symmetric-module comparison is supplied by `CompatibleModel`. -/
theorem contradiction_of_marked_linear_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (models : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          a6SynthemeStabilizer ∧ LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          BinaryFlags.H2 ∧ IntersectionBalance.CompatibleModel H V₃ V₁ a e))
    (hm : ∀ u ∈ c.Aone V₁, u ≠ 1 → ∃ n ∈ Source.QH H, n * u ≠ u * n)
    (hnf : letI := d.uh_elementary hHz
      ∀ u : Source.UH H V₃, (u : G) ∈ c.Aone V₁ → (u : G) ≠ 1 →
        ∃ g, a.action g (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ≠
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have marked : MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁ := by
    refine ⟨a, ?_⟩
    rcases models with ⟨e, hE, _⟩ | ⟨e, hE, he⟩
    · exact Or.inl ⟨e, hE⟩
    · exact Or.inr ⟨e, hE, he⟩
  have coords :
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom) := by
    rcases models with ⟨e, _, he⟩ | ⟨e, _, he⟩
    · exact Or.inl ⟨e, he⟩
    · exact Or.inr ⟨e, IntersectionBalance.CompatibleModel.action_cases H V₃ V₁ a e he⟩
  exact contradiction_of_linear_source d hHz hF9 c hH hgen hK hN hqs hcentral hcomm
    hstrict hDstrict marked a coords hm hnf

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
