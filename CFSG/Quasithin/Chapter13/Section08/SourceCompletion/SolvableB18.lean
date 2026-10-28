module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman

/-!
# The genuine B.1.8 input to the 13.8.5 transvection argument

The solvable factor theorem B.1.8(1)–(3) supplies exactly the universal
factor witness used in the solvable normal-closure branch. Applying the
already proved source theorem removes that callback from the literal
13.8.5 consumer. The corrected stable-family clause of B.1.8(5) is not
needed here. The separate earlier local-model, 13.7.6 and G.6.4 inputs
remain explicit.

Source: Aschbacher–Smith, B.1.8 and 13.8.5, printed pp.70 and 947–948.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component.RecognitionStep
open TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The universal B.1.8 factors, with exactly the action and source
hypotheses consumed by 13.8.5. -/
theorem solvable_ff_factors
    (B E : Type u) [Group B] [Finite B] [Group.IsSolvable B]
    [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) B E)
    (hc : pCore 2 B = ⊥) (hf : Function.Injective σ) (hff : IsFFModule σ) :
    Nonempty (ChapterB.SolvableFFFactors σ) :=
  (ChapterB.Glauberman.source_lemma_B_1_8_1_3 (ρ := σ) inferInstance hc hf hff).1

/-- The actual 13.8.5 source consumer with B.1.8 discharged. -/
theorem transvection_recognition
    (T : Sylow 2 G) {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      (∃ t : Source.Hstar H, IsTransvection ρ t) →
      (∃ K : Subgroup H, K.IsCComponent ∧
        (H : Set G) = (K.map H.subtype : Set G) * (T : Set G)) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁
        (le_sup_left.trans hH.1.2) ρ := by
  exact lemma_13_8_5 T d earlier localEarlier solvable_ff_factors hG64 hH

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
