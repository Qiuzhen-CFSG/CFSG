module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.QuasisimpleHead
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.LocalEmbedding

/-!
# Original source data for the local embedding classification

The original escaping setup supplies the actual strict overcomponent in
the second-vector centralizer, its full quotient Sylow subgroup, and the
proper local image of the original block. The quotient has trivial
two-core and is SQTK. Its smaller local subgroup has radical quotient A₅.
In the contained-layer case the head is quasisimple and that smaller
image is literally A₅; otherwise the natural A₅ block survives.

This collects the established source inputs to A.3.14 without asserting
its remaining carrier classification. Source: Aschbacher–Smith 10.2.1,
printed p.743, and A.3.14, printed pp.49–50.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_original_strict_component_local_embedding
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
            Nonempty (B ≃* alternatingGroup (Fin 5))) ∨ IsAlternatingBlock B 5) := by
  obtain ⟨t, ht, htn, p, hS, I, hLI, hIX, hI, hNI, hseven, hhead⟩ :=
    source_a5_original_strict_component_quasisimple_head D e hn hout
  have hv := (source_conjugate_layer_cubic_centralizes_original D e hn hout t p.second ht
    p.second_layer p.second_fixed p.second_ne p.second_opposite).1
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp
      ((D.simpleQTKE.involution_centralizer_sqtk hv).subgroup _)
  have hsqH : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_, hsqI.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho (pCore 2 I) pCore_isPGroup).trans
      (hsqI.stronglyQuasithin r hr ho)
  obtain ⟨S, hSm, hlocal, hnormal, htop, hproper, _⟩ :=
    source_a5_overcomponent_quotient_local_embedding D e hLI hIX hI hS
  obtain ⟨hradical, hsection⟩ :=
    source_a5_overcomponent_quotient_radical D e hLI hIX hI hS
  refine ⟨t, ht, htn, p, hv, hS, I, hLI, hIX, hI, hNI, hseven, hsqH,
    pCore_quotient_pCore_eq_bot 2, S, hSm, hlocal, hnormal, htop, hproper,
    hradical, hsection, ?_⟩
  rcases source_a5_overcomponent_layer_alternative D e hn hout hLI.le hIX hI hS with
    hcontained | hsurvives
  · have hquasi := hhead hcontained.1
    exact Or.inl ⟨hcontained.1, hquasi,
      source_a5_overcomponent_core_of_quasisimple_head
        D e hn hout hLI.le hIX hI hS hcontained.1 hquasi⟩
  · exact Or.inr hsurvives

end CFSG.Quasithin.Chapter10
