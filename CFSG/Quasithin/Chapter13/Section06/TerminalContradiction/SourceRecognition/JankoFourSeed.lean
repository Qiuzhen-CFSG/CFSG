module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ExceptionalKnownSimple
/-!
# Retaining quasisimplicity in the exceptional source lift

The actual exceptional local seed lies in the normal containing C-component.
Its image modulo the ambient two-core is quasisimple by the proved containing
argument. Transport through the intrinsic C-component quotient equivalence
retains this structure in the remaining J₄ alternative. No independent
simplicity certification for the J₄ presentation is required.

Source: Aschbacher–Smith A.3.12 and the component construction in 13.6.27.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.CandidateSelection Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {H : Type u} [Group H] [Finite H]
private theorem containing_quotient_quasisimple
    (hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (S : Sylow 2 H) {B K : Subgroup H} (hB : B ∈ Chapter1.L H S)
    (hc : Candidate (S : Subgroup H) B) (hK : K.IsCComponent) (hBK : B ≤ K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := pCore_isNilpotent (p := 2) (G := H)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hBbar : B.map q ∈ ChapterA.Section03.localCComponents Sbar := by
    simpa only [Sbar, q, Sylow.coe_mapSurjective] using
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
  exact IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
  (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
  (hcounter : IsA5Counterexample G)
  (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
include d hCv houtside hcounter h523

/-- The literal original source branch retains the proved quotient structure. -/
theorem source_jankoFour_quasisimple_or_global :
    (∃ K : Subgroup (centralizer (V₁ : Set G)), K.IsCComponent ∧ K.Normal ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) ∨ Source523.GlobalAlternative G := by
  let := d.elementary
  rcases omega_candidate_or_global_knownSimple d hCv houtside hcounter h523 with hl | hg
  · obtain ⟨KZ, hKZ, hcZ⟩ := hl
    obtain ⟨B, hB, hn, hc, _⟩ :=
      exists_normalized_local_candidate_in_singular_centralizer d KZ hKZ hcZ
    have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
      d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
    let S := T.subtype hTC
    have hH := SourceAbelian.point_centralizer_mem_family d houtside
    have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
    have hQ : IsSQTK KnownSimple.IsKnownSimple
        ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) := by
      refine ⟨?_, hsq.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hsq.stronglyQuasithin p hp ho)
    obtain ⟨K, hK, hnK, hBK, hcK | hj⟩ := normal_candidate_or_jankoFour hQ S hB hn hc
    · let := hnK
      let := hcK.quotient_isQuasisimple hK
      exact (terminal_contradiction_of_A5_source523_knownSimple d hCv houtside hcounter h523 hK hcK).elim
    · exact Or.inl ⟨K, hK, hnK, containing_quotient_quasisimple hQ S hB hc hK hBK, hj⟩
  · exact Or.inr hg
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
