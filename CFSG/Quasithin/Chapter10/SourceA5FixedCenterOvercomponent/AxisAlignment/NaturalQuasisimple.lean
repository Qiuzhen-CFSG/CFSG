module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalSurvivor
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedContaining

/-!
# The surviving original head is quasisimple

The actual surviving deleted-five block contributes an elementary sixteen
to the literal quotient I/O₂(I). The SQTK two-rank criterion excludes its
nonquasisimple C-component alternatives. This retains all original local
and Sylow markings for the remaining model exclusion.

Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original escaping setup has a quasisimple head containing the surviving deleted block. -/
theorem source_a5_original_natural_survivor_quasisimple
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
          IsAlternatingBlock B 5 := by
  obtain ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural⟩ :=
    source_a5_original_strict_component_natural_survivor D e hn hout
  have hqtop := SourceEmbeddings.alternatingFive_containing_component_quasisimple
    hqtk hO htop (show _ ≤ (⊤ : Subgroup (I ⧸ pCore 2 I)) from le_top) hnatural
  let := hqtop
  have hq : IsQuasisimple (I ⧸ pCore 2 I) := IsQuasisimple.of_mulEquiv topEquiv
  exact ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural⟩

end CFSG.Quasithin.Chapter10
