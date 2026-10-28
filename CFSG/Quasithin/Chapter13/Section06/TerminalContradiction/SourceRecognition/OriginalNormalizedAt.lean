module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscapeAt
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Application
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRightComplete

/-!
# The normalized residual branch at the original A₅ context

The actual A₅ quotient identifies L/O₂(L) with PSL₂(4). An isomorphism
of finite fields converts exclusion of the marked L₃(4) carrier into the
intrinsic PSL₃(4) exclusion. The original chosen module then supplies the
complete Chapter12 local preparation at exponent two, with the full
relative Borel normalizer and the literal two-residual quotient of H.

Uniqueness over L and completion recognition remain separate source inputs.
In particular the faithful local triple is not used as ambient recognition.
The M₂₂ exit is excluded by the original hypothesis; the remaining exits
give exactly the global alternative consumed by the residual split.
The Cartan escape branch is independent and remains explicit.

Source: Aschbacher--Smith, 5.2.3--6, pp.649--651, and 13.6.27, pp.934--935.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Chapter12.Section02 Chapter6.Source.RankOneGeneric

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

private theorem original_linear_quotient (d : Context T L V V₁ V₂ V₃) :
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2) := by
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by decide), ?_⟩
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact ⟨d.quotient.trans e.symm⟩

private theorem original_intrinsic_three_exclusion {X : Type*} [Group X]
    (h : ¬ Nonempty (X ≃* Components.L3Four)) : ¬ ClassicalGroup.IsPSL X 3 4 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Components.F4
  let eF : F ≃+* Components.F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact (GaloisField.card 2 2 (by decide)).symm)
  exact h ⟨e.trans (Atlas.fieldEquivPSL 3 eF)⟩

/-- The complete normalized adapter at the selected H. The recognition
premise is literally the shared Chapter12 completion premise at exponent two. -/
theorem source523_global_of_normalized_rankOne_at (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Components.L3Four))
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : Source523.GlobalAlternative G := by
  have h := original_hypothesis1223 d
  have hexit := d.chosen.rankOne_globalExit_of_uniqueness_and_recognition h hmany
    (by decide : 1 < 2) (original_linear_quotient d) hH hgen
    (original_intrinsic_three_exclusion hthree) hN hunique hrecognize
  rcases hexit with ⟨f, _, hf⟩ | h22 | h23
  · exact Or.inr ⟨f, hf⟩
  · exact (h.no_M22 h22).elim
  · exact Or.inl h23

/-- The actual terminal consumer: linear residuals are already excluded,
Cartan escape supplies the local alternative, and the normalized branch
uses the constructed Chapter12 pair with its explicit completion input. -/
theorem source_qtkeModel_of_original_rankOne_sources_at
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hescape : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
      ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Components.L3Four) →
      ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
        normalizer ((pResidual 2 H).map H.subtype : Set G) →
      Source523.LocalAlternative T L H V 2)
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hrecognize : ∀ H : Subgroup G,
      H ≤ centralizer (V₁ : Set G) →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : ClassificationModels.IsQTKEModel G := by
  apply source_qtkeModel_of_residual_branches d hCv houtside hcounter hescape
  intro H hH hHC hgen hthree hN
  exact source523_global_of_normalized_rankOne_at d hmany hH hgen hthree hN
    hunique (hrecognize H hHC)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
