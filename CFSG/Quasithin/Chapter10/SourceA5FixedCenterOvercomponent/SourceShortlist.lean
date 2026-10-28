module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.LocalEmbedding
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveShortlist

/-!
# The original contained-A₅ shortlist

Apply the genuine local embedding classification to the actual quotient
I/O₂(I) produced by the original escaping setup. Every contained-layer
branch now has its complete carrier shortlist, including the possible
central triple cover of A₇. The surviving natural A₅-block branch is
retained explicitly for its separate source exclusion.

Source: Aschbacher--Smith 10.2.1, printed p.743; A.3.14, pp.49--50.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Only the original assumptions are used; the surviving block is the
sole alternative to the complete contained-A₅ carrier shortlist. -/
theorem source_a5_original_strict_component_shortlist_or_block
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (L : Set G) ∧
      ∃ p : SourceA5OriginalFixedPair D t,
      orderOf p.second = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
        (centralizer ({p.second} : Set G)) ∧
      ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({p.second} : Set G) ∧
        (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent ∧
        centralizer ({p.second} : Set G) ≤ normalizer (I : Set G) ∧
        ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) ∧
        IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) ∧
        pCore 2 (I ⧸ pCore 2 I) = ⊥ ∧
        ∃ S : Sylow 2 I,
          (S : Subgroup I).map I.subtype =
            ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊓ I ∧
          let K := L.subgroupOf I
          let q := QuotientGroup.mk' (pCore 2 I)
          let B := K.map q
          let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
          B ∈ localCComponents Sbar ∧
          (Sbar : Subgroup (I ⧸ pCore 2 I)) ≤ normalizer (B : Set _) ∧
          (⊤ : Subgroup (I ⧸ pCore 2 I)).IsCComponent ∧ B ≠ ⊤ ∧
          solvableRadical B = pCore 2 B ∧
          Nonempty ((B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 5)) ∧
          (((blockU K).map K.subtype ≤ pCore 2 I ∧
            IsQuasisimple (I ⧸ pCore 2 I) ∧
            K.pCoreIn 2 ≤ pCore 2 I ∧
            (q.subgroupMap K).ker = pCore 2 K ∧
            Nonempty (B ≃* alternatingGroup (Fin 5)) ∧
            SourceEmbeddings.AlternatingFive.Shortlist (I ⧸ pCore 2 I)) ∨ IsAlternatingBlock B 5) := by
  obtain ⟨t, ht, htn, p, hv, hS, I, hLI, hIX, hI, hNI, hseven, hsq, hcore,
    S, hSm, hl, hnormal, htop, hproper, hradical, hsection, hcase⟩ :=
    source_a5_original_strict_component_local_embedding D e hn hout
  refine ⟨t, ht, htn, p, hv, hS, I, hLI, hIX, hI, hNI, hseven, hsq, hcore,
    S, hSm, hl, hnormal, htop, hproper, hradical, hsection, ?_⟩
  rcases hcase with ⟨hu,hq,hk,hker,⟨eb⟩⟩ | hb
  · let := hq
    exact .inl ⟨hu,hq,hk,hker,⟨eb⟩,
      SourceEmbeddings.AlternatingFive.shortlist_knownSimple hsq hcore
        (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))) hl hnormal eb hproper⟩
  · exact .inr hb

end CFSG.Quasithin.Chapter10
