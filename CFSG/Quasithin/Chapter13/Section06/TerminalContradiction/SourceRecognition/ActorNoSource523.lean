module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ActionKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorCentralizerBoundSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Normalization
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.FiveDivisorNormalization
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourAction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.J2KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceContextConstituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SuzukiFixedImage.Centralizer
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.FaithfulExceptional

/-!
# The extra-component actor contradiction before uniqueness

The actual binary actor on the singular-centralizer quotient is retained while
an extra Suzuki component is present. Its conjugation kernel is bounded by the
proved PSL₃(4)/M₂₃ automorphism bound. Steinberg fixation places that same
actor in the literal Suzuki centralizer. Restriction to this centralizer is
faithful and still has ratio at most two, while its exceptional generalized
Fitting subgroup has strict ratio greater than two. This discharges the
second component-uniqueness use of the old source 5.2.3 premise.

The candidate/seed selection use of 5.2.3 remains upstream and is intentionally
not hidden by this extension.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Ratio.StrictBound Section05.A5Source CentralizerReduction CentralizerReduction.A5Module Section08
open Components Components.SuzukiIsolation Components.SuzukiIsolation.ActorKernel
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Ratio.SuzukiFixedImage
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- An additional Suzuki component contradicts the bounded faithful source
actor in the M₂₃ or PSL₃(4) candidate rows. All kernel, image and source-span
premises are constructed from the original context. -/
theorem extra_component_contradiction_m23_or_l3
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23))
    {D : Subgroup (centralizer (V₁ : Set G))}
    (hD : D.IsCComponent) (hne : D ≠ K) : False := by
  let H : Subgroup G := centralizer (V₁ : Set G)
  have hHmem := SourceAbelian.point_centralizer_mem_family d houtside
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hHmem.1.1
  have hfive : primeRank 5 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 5 (by decide) _ pCore_isPGroup).trans
      (hSQ.stronglyQuasithin 5 (by decide) (by decide))
  obtain ⟨m, hm, ⟨e⟩⟩ := ActorKernel.other_suzuki hSQ hK hc hD hne
  let := suzuki_component_normal hK hc hD hne hm e hfive
  obtain ⟨hU, hn, hk, hfaith, hratio⟩ :=
    source_bounded_faithful_action_of_context d hCv houtside hcounter
  let _ := hU
  obtain ⟨B, hB, hquad, hsmall⟩ :=
    (quadraticRatio_le_two_iff _).mp hratio
  let F := AlgebraicClosure (SuzukiNatural.F m)
  let D₀ : Subgroup G := D.map H.subtype
  let i : D ≃* D₀ := D.equivMapOfInjective H.subtype H.subtype_injective
  let e₀ : (D₀ ⧸ pCore 2 D₀) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).symm.trans e
  let : IsElementaryAbelian 2 B := hB.2
  obtain ⟨f, hspan, _⟩ :=
    Components.SuzukiIsolation.source_context_constituents d hCv houtside hcounter
      hn hk D hD hm e F
  have hker : Nat.card ((centralizer
      (Source.starImage H D₀ : Set (Source.Hstar H))).subgroupOf B) ≤ 256 := by
    simpa only [D₀, source_component_starImage H D] using
      (ActorKernel.centralizer_card_le_256_of_context d hCv houtside hcounter hK hD hne B
        hc (IsElementaryAbelian.isPGroup 2 B) hmodel)
  have hspan₀ : ∃ f : SuzukiMatrixGroup m ≃* ((D₀) ⧸ pCore 2 D₀),
      typeSpan ((extendScalars F (representation H V₃ V₁ hn)).comp (D₀.subgroupOf H).subtype)
          (trivial F (D₀.subgroupOf H) F) ⊔
        typeSpan ((extendScalars F (representation H V₃ V₁ hn)).comp (D₀.subgroupOf H).subtype)
          (markedComponentSteinberg (show D₀ ≤ H from map_subtype_le D) F f) = ⊤ := by
    change ∃ f : SuzukiMatrixGroup m ≃* ((D.map H.subtype) ⧸ pCore 2 (D.map H.subtype)), _
    exact ⟨f, hspan⟩
  have hBD : B ≤ centralizer (Source.starImage H D₀ : Set (Source.Hstar H)) :=
    source_small_actor_le_centralizer_of_binary_budget
      (show D₀ ≤ H from map_subtype_le D) (source_component_normalizer H D) hn hk hm F e₀ hspan₀ B hB hquad (le_trans hker (by omega)) hsmall
  have hSQstar : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H) := by
    refine ⟨?_, hSQ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hSQ.stronglyQuasithin p hp ho)
  have hBD' : B ≤ centralizer (D.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
    simpa only [D₀, source_component_starImage H D] using hBD
  obtain ⟨hfaithC, hsqC, hBC, hquadC, hrankC, hcodimC, hratioC⟩ :=
    same_actor_on_centralizer (starRepresentation H V₃ V₁ hn hk) hfaith hSQstar
      (D.map (QuotientGroup.mk' (pCore 2 H))) B hBD' hB hquad hsmall
  obtain ⟨hF, hcenterF, ⟨eC⟩⟩ :=
    ActorKernel.centralizer_structure_of_context d hCv houtside hcounter hK hc hD hne
  let C := centralizer (D.map (QuotientGroup.mk' (pCore 2 H)) :
      Set (H ⧸ pCore 2 H))
  let : IsQuasisimple (K ⧸ pCore 2 K) := inferInstance
  let : IsQuasisimple (generalizedFitting C) :=
    IsQuasisimple.of_mulEquiv eC.symm
  have hmodelC : ExceptionalModel (generalizedFitting C) := by
    unfold ExceptionalModel
    rcases hmodel with hmodel | hmodel
    · obtain ⟨g⟩ := hmodel
      exact Or.inl ⟨eC.trans g⟩
    · obtain ⟨g⟩ := hmodel
      exact Or.inr (Or.inl ⟨eC.trans g⟩)
  have hstrict := FaithfulExceptional.quadraticRatio_gt_two
    ((starRepresentation H V₃ V₁ hn hk).comp C.subtype) hfaithC hsqC
      (inferInstance : IsQuasisimple (generalizedFitting C)) hmodelC
  exact (not_lt_of_ge hratioC) hstrict

/-- The M₂₃/PSL₃(4) candidate component is unique without the old
universal source 5.2.3 theorem. -/
theorem source_component_unique_no_source523_m23_or_l3
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) :
    ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K := by
  intro D hD
  by_cases hne : D = K
  · exact hne
  · exact (extra_component_contradiction_m23_or_l3 d hCv houtside hcounter hK hc hmodel hD hne).elim

/-- The actual M₂₃/PSL₃(4) candidate terminal contradiction. This is
an application of the no-source-5.2.3 uniqueness theorem above to the
existing component conclusion and terminal source consumer. -/
theorem terminal_contradiction_of_A5_candidate_no_source523_m23_or_l3
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) : False := by
  exact terminal_contradiction_of_A5_context_knownSimple d hCv houtside hcounter
    (source_component_conclusion_of_context_knownSimple d hCv houtside hcounter hK hc
      (source_component_unique_no_source523_m23_or_l3 d hCv houtside hcounter hK hc hmodel))

omit [IsElementaryAbelian 2 V] in
/-- An additional Suzuki component also contradicts the bounded faithful
source actor in the J₄ candidate row. The J₄ centralizer is identified by the
proved full-innerness equivalence, so the concrete J₄ ratio theorem applies
directly to the restricted original action. -/
theorem extra_component_contradiction_jankoFour
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (eK : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    {D : Subgroup (centralizer (V₁ : Set G))}
    (hD : D.IsCComponent) (hne : D ≠ K) : False := by
  let H : Subgroup G := centralizer (V₁ : Set G)
  have hHmem := SourceAbelian.point_centralizer_mem_family d houtside
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hHmem.1.1
  have hfive : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr eK.toEquiv, Janko4.Cardinality.model_card]
    decide
  have hrank : primeRank 5 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 5 (by decide) _ pCore_isPGroup).trans
      (hSQ.stronglyQuasithin 5 (by decide) (by decide))
  obtain ⟨m, hm, ⟨e⟩⟩ := ActorKernel.other_suzuki_of_jankoFour hSQ hK eK hD hne
  let := suzuki_component_normal_of_five_dvd hK hfive hD hne hm e hrank
  obtain ⟨hU, hn, hk, hfaith, hratio⟩ :=
    source_bounded_faithful_action_of_context d hCv houtside hcounter
  let _ := hU
  obtain ⟨B, hB, hquad, hsmall⟩ :=
    (quadraticRatio_le_two_iff _).mp hratio
  let F := AlgebraicClosure (SuzukiNatural.F m)
  let D₀ : Subgroup G := D.map H.subtype
  let i : D ≃* D₀ := D.equivMapOfInjective H.subtype H.subtype_injective
  let e₀ : (D₀ ⧸ pCore 2 D₀) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).symm.trans e
  let : IsElementaryAbelian 2 B := hB.2
  obtain ⟨f, hspan, _⟩ :=
    Components.SuzukiIsolation.source_context_constituents d hCv houtside hcounter
      hn hk D hD hm e F
  have hker : Nat.card ((centralizer
      (Source.starImage H D₀ : Set (Source.Hstar H))).subgroupOf B) ≤ 2048 := by
    simpa only [D₀, source_component_starImage H D] using
      (ActorKernel.centralizer_card_le_2048_of_context_jankoFour d hCv houtside hcounter
        (hK := hK) (hD := hD) (hne := hne) B eK)
  have hspan₀ : ∃ f : SuzukiMatrixGroup m ≃* ((D₀) ⧸ pCore 2 D₀),
      typeSpan ((extendScalars F (representation H V₃ V₁ hn)).comp (D₀.subgroupOf H).subtype)
          (trivial F (D₀.subgroupOf H) F) ⊔
        typeSpan ((extendScalars F (representation H V₃ V₁ hn)).comp (D₀.subgroupOf H).subtype)
          (markedComponentSteinberg (show D₀ ≤ H from map_subtype_le D) F f) = ⊤ := by
    change ∃ f : SuzukiMatrixGroup m ≃* ((D.map H.subtype) ⧸ pCore 2 (D.map H.subtype)), _
    exact ⟨f, hspan⟩
  have hBD : B ≤ centralizer (Source.starImage H D₀ : Set (Source.Hstar H)) :=
    source_small_actor_le_centralizer_of_binary_budget
      (show D₀ ≤ H from map_subtype_le D) (source_component_normalizer H D) hn hk hm F e₀ hspan₀ B hB hquad hker hsmall
  have hSQstar : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H) := by
    refine ⟨?_, hSQ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hSQ.stronglyQuasithin p hp ho)
  have hBD' : B ≤ centralizer (D.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
    simpa only [D₀, source_component_starImage H D] using hBD
  obtain ⟨hfaithC, hsqC, hBC, hquadC, hrankC, hcodimC, hratioC⟩ :=
    same_actor_on_centralizer (starRepresentation H V₃ V₁ hn hk) hfaith hSQstar
      (D.map (QuotientGroup.mk' (pCore 2 H))) B hBD' hB hquad hsmall
  have eC := ActorKernel.jankoFour_centralizerEquiv d hCv houtside hcounter hK eK hD hne
  let : IsSimpleGroup (K ⧸ pCore 2 K) := jankoFour_quotient_isSimple eK
  let : IsSimpleGroup Janko4.Model := eK.symm.isSimpleGroup
  let : IsSimpleGroup (centralizer (D.map (QuotientGroup.mk' (pCore 2 H)) :
      Set (H ⧸ pCore 2 H))) := eC.isSimpleGroup_congr.mpr (by infer_instance)
  have hstrict := Janko4.BinaryDegree.quadraticRatio_gt_two
    ((starRepresentation H V₃ V₁ hn hk).comp
      (centralizer (D.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))).subtype)
    hfaithC eC
  exact (not_lt_of_ge hratioC) hstrict

omit [IsElementaryAbelian 2 V] in
/-- The J₄ candidate component is unique without the old universal source
5.2.3 theorem. -/
theorem source_component_unique_no_source523_jankoFour
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (eK : (K ⧸ pCore 2 K) ≃* Janko4.Model) :
    ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K := by
  intro D hD
  by_cases hne : D = K
  · exact hne
  · exact (extra_component_contradiction_jankoFour d hCv houtside hcounter hK eK hD hne).elim

omit [IsElementaryAbelian 2 V] in
/-- The J₄ candidate terminal contradiction after actor-based uniqueness. -/
theorem terminal_contradiction_of_A5_candidate_no_source523_jankoFour
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (eK : (K ⧸ pCore 2 K) ≃* Janko4.Model) : False := by
  exact terminal_contradiction_of_A5_jankoFour_of_unique d hCv houtside hcounter hK eK
    (source_component_unique_no_source523_jankoFour d hCv houtside hcounter hK eK)

/-- Dispatch the complete actual candidate catalogue. J₂ is closed by the
existing odd-rank source argument; M₂₃ and PSL₃(4) use the actor-based
extra-component contradiction above. This removes only the uniqueness use of
source 5.2.3 while preserving the independent candidate-selection premise. -/
theorem terminal_contradiction_of_A5_candidate_no_source523
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K) : False := by
  rcases hc with hJ | hc'
  · obtain ⟨e⟩ := hJ
    exact terminal_contradiction_of_A5_j2_knownSimple d hCv houtside hcounter hK e
  rcases hc' with hM | hL
  · obtain ⟨e⟩ := hM
    exact terminal_contradiction_of_A5_candidate_no_source523_m23_or_l3 d hCv houtside
      hcounter hK (Or.inr (Or.inl (Nonempty.intro e)))
      (hmodel := Or.inr (Nonempty.intro e))
  · obtain ⟨e, hDynkin⟩ := hL
    exact terminal_contradiction_of_A5_candidate_no_source523_m23_or_l3 d hCv houtside
      hcounter hK (Or.inr (Or.inr ⟨e, hDynkin⟩))
      (hmodel := Or.inl (Nonempty.intro e))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
