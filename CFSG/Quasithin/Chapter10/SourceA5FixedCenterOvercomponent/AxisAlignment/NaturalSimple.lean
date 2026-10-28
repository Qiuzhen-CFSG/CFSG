module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalQuasisimple
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter

/-!
# The original deleted block in its simple central quotient

The source survivor has a quasisimple head. We retain every original pair,
centralizer, component and Sylow marking and additionally pass its actual
block to the simple central quotient. The mapped block remains proper and
is normalized by the mapped full Sylow. Theorem C applies to that same
quotient through Theorem A's semisimple-section rank bound.

Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The surviving original deleted block embeds properly in the literal simple central quotient. -/
theorem source_a5_original_natural_survivor_simple_quotient
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
        IsQuasisimple (I ⧸ pCore 2 I) ∧
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
          IsAlternatingBlock B 5 ∧
          let r := QuotientGroup.mk' (center (I ⧸ pCore 2 I))
          let C := B.map r
          let Sbb := Sbar.mapSurjective
            (QuotientGroup.mk'_surjective (center (I ⧸ pCore 2 I)))
          IsSimpleGroup ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ∧
          ChapterA.Section02.IsTheoremCModel
            ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ∧
          C ∈ localCComponents Sbb ∧
          (Sbb : Subgroup ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I))) ≤
            normalizer (C : Set ((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I))) ∧
          IsAlternatingBlock C 5 ∧ C ≠ ⊤ := by
  obtain ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural⟩ :=
    source_a5_original_natural_survivor_quasisimple D e hn hout
  let := hq
  exact ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural,IsQuasisimple.simple,
    SourceEmbeddings.quasisimple_center_quotient_theoremC_model hqtk,
    SourceEmbeddings.alternatingFive_block_center_image
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I)))
      hB hSB hnatural hproper⟩

end CFSG.Quasithin.Chapter10
