module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalNormalizedAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniquenessSourceMS

/-!
# Original nonblock exclusion in the terminal normalized branch

The original A₅ context supplies the same chosen module and PSL₂(4) quotient.
Apply the complete local-selection/right-factor construction at that original
L, transporting only the field-four quotient marking and the intrinsic
PSL₃(4) exclusion. The literal selected-H residual split then consumes this
normalized branch and retains the full IsQTKEModel conclusion.

The original callback APIs remain available. The specialized MS applications
discharge that callback by the action-only contradiction, retaining just the
original full-quotient selection and genuine C.1.34 alternatives. Their named
producers are qt-d-1222-rankone-uniqueness-nonblock and
qt-c134-nonbinary-linear-three-source. No secondary-core enlargement is needed.
Cartan escape and genuine ambient completion recognition retain their separate
producers. No later theorem is used to prove uniqueness.
Source: Aschbacher–Smith 4.3.2–16, pp.613–618; 5.2.3–6, pp.649–651;
13.6.27, pp.934–935.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Chapter12.Section02 Chapter6.Source.RankOneGeneric

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Apply original nonblock exclusion at the same L and selected H. The
right factor and local selection are constructed; completion recognition
retains its original source premise at exponent two. -/
theorem source523_global_of_normalized_nonblock_at (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Components.L3Four))
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hnonblock : ∀ c : Chapter4.Section03.RankOneUniqueness.SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : Source523.GlobalAlternative G := by
  have h := original_hypothesis1223 d
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2) := by
    refine ⟨GaloisField 2 2, inferInstance, inferInstance,
      GaloisField.card 2 2 (by decide), ?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  have hthree' : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 := by
    rintro ⟨F, _, _, hF, ⟨e⟩⟩
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Components.F4
    let eF : F ≃+* Components.F4 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
      exact (GaloisField.card 2 2 (by decide)).symm)
    exact hthree ⟨e.trans (Atlas.fieldEquivPSL 3 eF)⟩
  have hexit := d.chosen.rankOne_globalExit_of_nonblock_exclusion_and_recognition h hmany
    (by decide : 1 < 2) hpsl hH hgen hthree' hN hnonblock hrecognize
  rcases hexit with ⟨f, _, hf⟩ | h22 | h23
  · exact Or.inr ⟨f, hf⟩
  · exact (h.no_M22 h22).elim
  · exact Or.inl h23

/-- The original terminal residual split now consumes the nonblock exclusion
directly. The independent Cartan escape and genuine completion recognition
remain explicit, and the conclusion retains the full known-simple catalogue. -/
theorem source_qtkeModel_of_original_nonblock_sources_at
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
    (hnonblock : ∀ c : Chapter4.Section03.RankOneUniqueness.SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
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
  exact source523_global_of_normalized_nonblock_at d hmany hH hgen hthree hN
    hnonblock (hrecognize H hHC)

/-- The normalized original branch consumes the genuine marked MS selection.
The action-only contradiction discharges its nonblock callback at the same
chosen module; completion recognition remains an independent source input. -/
theorem source523_global_of_normalized_originalMSAlternatives_at
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Components.L3Four))
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hms : ∀ c : Chapter4.Section03.RankOneUniqueness.SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Chapter4.Section03.RankOneUniqueness.Nonblock.OriginalMSAlternatives c)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : Source523.GlobalAlternative G :=
  source523_global_of_normalized_nonblock_at d hmany hH hgen hthree hN
    (fun c hf hb => Chapter4.Section03.RankOneUniqueness.Nonblock.false_of_originalMSAlternatives
      d.chosen (original_hypothesis1223 d) hf hb (hms c hf hb)) hrecognize

/-- The literal selected-H residual split now takes only the original MS
selection from the nonblock family. Cartan escape and ambient recognition
remain explicit, and the conclusion is the full known-simple catalogue. -/
theorem source_qtkeModel_of_original_ms_sources_at
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
    (hms : ∀ c : Chapter4.Section03.RankOneUniqueness.SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Chapter4.Section03.RankOneUniqueness.Nonblock.OriginalMSAlternatives c)
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
  exact source523_global_of_normalized_originalMSAlternatives_at d hmany hH hgen hthree hN
    hms (hrecognize H hHC)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
