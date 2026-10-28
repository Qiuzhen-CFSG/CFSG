module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.OmegaKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LocalTransport
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ActorNoSource523
public import CFSG.KnownSimple.CarrierCatalogue.ClassificationInclusion
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# A single earlier classification at the original A₅ outside subgroup

The exceptional component of the central omega centralizer is transported to
C_G(V₁), then lifted by the proved exceptional embedding catalogue. Both the
ordinary candidates and its J₄ enlargement are excluded using the original
faithful actor. Consequently one local application of 5.2.3 suffices; neither
its universal formulation nor a second use for uniqueness is needed here.

The PSL₃(4) residual branch is excluded directly inside C_G(V₁): its
two-perfect residual is a C-component, minimal parabolicity supplies the
diagram action, and the same lifting argument applies. The last theorem
retains only two independent earlier source branches on the actual HStar
subgroup: failure of normalization by N_L(T∩L), and the normalized
non-PSL₃(4) case. These two inputs remain unproved source obligations.
The terminal assembly is conditional on them; it does not prove 5.2.3. No new candidate or source-context record is introduced.

Source: Aschbacher–Smith, 5.1.14, 5.2.2, 5.2.3 and §§5.2–5.3,
printed pp.638–661; the application in 13.6.27, pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.CandidateSelection Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Exclude an actual local candidate in the singular centralizer without
an earlier classifier or an embedding callback. The J₄ containing row is retained and excluded
by the same source actor, rather than assumed absent from the catalogue. -/
theorem terminal_contradiction_of_local_candidate
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {B : Subgroup (centralizer (V₁ : Set G))}
    (hB : B ∈ Chapter1.L (centralizer (V₁ : Set G))
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))))
    (hn : (T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)) ≤ normalizer (B : Set _))
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) B) : False := by
  let := d.elementary
  let H := centralizer (V₁ : Set G)
  have hTC : (T : Subgroup G) ≤ H :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  let S := T.subtype hTC
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨K, hK, hnK, hBK, hcK | hj⟩ := normal_candidate_or_jankoFour hQ S hB hn hc
  · let := hnK
    let := hcK.quotient_isQuasisimple hK
    exact terminal_contradiction_of_A5_candidate_no_source523 d hCv houtside hcounter hK hcK
  · let := hnK
    obtain ⟨eK⟩ := hj
    let := pCore_isNilpotent (p := 2) (G := H)
    let q := QuotientGroup.mk' (pCore 2 H)
    let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    have hBbar : B.map q ∈ ChapterA.Section03.localCComponents Sbar := by
      simpa only [Sbar, q, S, Sylow.coe_mapSurjective, Sylow.coe_subtype] using
        Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
    have hm : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel (B ⧸ pCore 2 B) := by
      rcases hc with hJ | hM | ⟨e, _⟩
      · exact Or.inl hJ
      · exact Or.inr (Or.inl hM)
      · exact Or.inr (Or.inr ⟨e⟩)
    let eB : (B ⧸ pCore 2 B) ≃* ((B.map q) ⧸ pCore 2 (B.map q)) := by
      apply MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B) (q.subgroupMap_surjective B)
      rw [ker_subgroupMap, QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    let : IsQuasisimple (K.map q) :=
      ChapterA.Section03.SourceEmbeddings.Exceptional.containing_quasisimple hQ
        (pCore_quotient_pCore_eq_bot 2) Sbar hBbar (hK.map_quotient _) (map_mono hBK)
        (hm.of_equiv eB.symm)
    let : IsQuasisimple (K ⧸ pCore 2 K) :=
      IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm
    exact terminal_contradiction_of_A5_candidate_no_source523_jankoFour
      d hCv houtside hcounter hK eK

/-- The original central-omega candidate maps to a local candidate in
C_G(V₁), which the preceding theorem excludes. -/
theorem terminal_contradiction_of_omega_candidate
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {KZ : Subgroup (centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))}
    (hKZ : KZ.IsCComponent)
    (hcZ : Candidate ((T : Subgroup G).subgroupOf (centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))) KZ) : False := by
  obtain ⟨B, hB, hn, hc, _⟩ :=
    exists_normalized_local_candidate_in_singular_centralizer d KZ hKZ hcZ
  exact terminal_contradiction_of_local_candidate d hCv houtside hcounter hB hn hc

/-- The linear-three residual branch needs no 5.1.14 classification here:
the actual outside H already lies in C_G(V₁), where its residual is a local
candidate with the nontrivial diagram action forced by minimal parabolicity. -/
theorem terminal_contradiction_of_linear_residual
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (e : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) : False := by
  let := d.elementary
  obtain ⟨s, _, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  have hns : ¬ Group.IsSolvable H := by
    intro hs
    exact hH.1.2 ((source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 H hH.1.1 hs)
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  have hR : (pResidual 2 H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (pResidual 2 H).Normal).isSubnormal (isPPerfect_pResidual 2)
  let B := (pResidual 2 H).map (inclusion hHC)
  have hB : B ∈ Chapter1.L (centralizer (V₁ : Set G))
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) :=
    local_component_map_of_HOver T hH.1.1 hHC (pResidual 2 H) hR
  have hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) B := by
    apply linear_candidate_of_HStar_nonsolvable T d.normalizes_L hH hns hHC e B
    rw [map_map]
    rfl
  have hnorm := (le_normalizer_of_normal : (⊤ : Subgroup H) ≤
      normalizer (pResidual 2 H : Set H))
  have hn : (T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)) ≤ normalizer (B : Set _) := by
    have hS : ((T : Subgroup G).subgroupOf H).map (inclusion hHC) =
        (T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)) := by
      apply map_injective (centralizer (V₁ : Set G)).subtype_injective
      rw [map_map, map_subgroupOf_eq_of_le (hH.1.1.2.trans hHC)]
      exact map_subgroupOf_eq_of_le hH.1.1.2
    rw [← hS]
    exact (map_mono (le_top.trans hnorm)).trans (le_normalizer_map (inclusion hHC))
  exact terminal_contradiction_of_local_candidate d hCv houtside hcounter hB hn hc

/-- Apply the full terminal argument to a single selected source seed.
The A₇ exclusion and actual linear diagram action use that same seed. -/
theorem terminal_contradiction_of_selected_seed
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (seed : SelectedSeed T (normalizer (L : Set G))) : False := by
  let := d.elementary
  obtain ⟨s, _, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  exact terminal_contradiction_of_omega_candidate d hCv houtside hcounter
    seed.component (seed.candidate d s)

/-- The local alternative of one 5.2.3 application is impossible. Residual
normalization, generation, escape and nonsolvability are derived here. -/
theorem terminal_contradiction_of_local_source523
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : 1 < ChapterE.generationParameter H)
    (hl : Source523.LocalAlternative T L H V 2) : False := by
  let := d.elementary
  obtain ⟨s, _, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hgen := congrArg (map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] at hgen
  have hout : ¬ (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) := by
    intro hR
    exact hH.1.2 (hgen ▸ sup_le hR d.normalizes_L)
  have hTR : (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
    hTH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have hns : ¬ Group.IsSolvable H := by
    intro hsol
    exact hH.1.2 ((source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 H hH.1.1 hsol)
  obtain ⟨_, _, K, hK, hRK, hm⟩ := hl
  exact terminal_contradiction_of_selected_seed d hCv houtside hcounter {
    H := H
    star := hH
    parameter := hn
    nonsolvable := hns
    K := K
    component := hK
    contains := hRK
    residual_generates := hgen
    normalizes := normalizes_component_over_residual T H _
      (sylow_le_omega_centralizer T) hns hTR hK hRK
    residual_outside := hout
    models := hm }

/-- A single literal earlier-source application suffices for the full
Main Theorem catalogue, without either universal earlier callback. -/
theorem source_qtkeModel_of_source523_at_H
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : 1 < ChapterE.generationParameter H)
    (h523 : Source523.LocalAlternative T L H V 2 ∨ Source523.GlobalAlternative G) :
    ClassificationModels.IsQTKEModel G := by
  rcases h523 with hl | hm | ⟨f, hf⟩
  · exact (terminal_contradiction_of_local_source523 d hCv houtside hcounter hH hn hl).elim
  · exact .sporadic ⟨.m23, hm⟩
  · exact .rank_two f hf

/-- The two remaining earlier-source branches, specialized to the actual
A₅ context and its outside subgroup in C_G(V₁). Their proofs remain with
independent source producers. The full relative normalizer N_L(T∩L) is
mapped into G, so the split does not choose or change a Cartan marking. -/
theorem source_qtkeModel_of_residual_branches
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hescape : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
      ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) →
      ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
        normalizer ((pResidual 2 H).map H.subtype : Set G) →
      Source523.LocalAlternative T L H V 2)
    (hnormalized : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
      ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) →
      (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
        normalizer ((pResidual 2 H).map H.subtype : Set G) →
      Source523.GlobalAlternative G) : ClassificationModels.IsQTKEModel G := by
  let := d.elementary
  obtain ⟨H, hH, hHC, hn, _, _, _⟩ :=
    source_initial_residual_of_context_knownSimple d hCv houtside hcounter
  apply source_qtkeModel_of_source523_at_H d hCv houtside hcounter hH hn
  by_cases hl : Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four)
  · exact (terminal_contradiction_of_linear_residual d hCv houtside hcounter hH hHC hl.some).elim
  by_cases hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer ((pResidual 2 H).map H.subtype : Set G)
  · exact Or.inr (hnormalized H hH hHC hn hl hN)
  · exact Or.inl (hescape H hH hHC hn hl hN)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
