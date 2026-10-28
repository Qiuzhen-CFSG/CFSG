module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalSporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedM24

/-!
# Removing M24 from the original positive-center deleted-block survivor

The literal double quotient, mapped block and mapped full Sylow produced
by the original source reduction satisfy the native M24 exclusion. All
original pair, centralizer and component witnesses remain unchanged.
The remaining simple carriers are J4, Held and Rudvalis.

Source: Aschbacher–Smith 10.2.1, printed p.743, inspecting A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original source survivor retains only J4, Held and Rudvalis. -/
theorem source_a5_original_natural_survivor_without_m24
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
          IsAlternatingBlock C 5 ∧ C ≠ ⊤ ∧
          ∃ name : ClassificationModels.SporadicName,
            (name = .j4 ∨ name = .he ∨ name = .ru) ∧
            Nonempty (((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ≃* name.Carrier) := by
  obtain ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural,hsimple,hmodel,hC,hSC,hCblock,hCproper,
    name,hname,he⟩ := source_a5_original_natural_survivor_sporadic D e hn hout
  let := hq
  let := hsimple
  refine ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural,hsimple,hmodel,hC,hSC,hCblock,hCproper,?_⟩
  rcases hname with hm | hm
  · subst name
    exact (SourceEmbeddings.alternatingFiveDeleted_not_m24 he.some
      ((S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))).mapSurjective
        (QuotientGroup.mk'_surjective (center (I ⧸ pCore 2 I))))
      _ hCblock hC hSC).elim
  · exact ⟨name,hm,he⟩

end CFSG.Quasithin.Chapter10
