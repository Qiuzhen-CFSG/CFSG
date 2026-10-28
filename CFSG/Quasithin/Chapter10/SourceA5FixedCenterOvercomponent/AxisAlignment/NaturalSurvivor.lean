module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SourceShortlist
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.OriginalRecognition

/-!
# Elimination of the original contained-layer branch

The actual local A₅ shortlist and the faithful chief action force I/O₂(I)
to be A₇ in the contained-layer case. The original commuting cubic has
already excluded that quotient. Therefore the original escaping setup
must produce a surviving natural A₅ block in its head. This theorem
retains every original local embedding and Sylow marking for the remaining
source exclusion; it does not assert that exclusion.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original source hypotheses reduce to the sole surviving natural-block case. -/
theorem source_a5_original_strict_component_natural_survivor
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
          IsAlternatingBlock B 5 := by
  obtain ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hcases⟩ :=
    source_a5_original_strict_component_shortlist_or_block D e hn hout
  refine ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,?_⟩
  rcases hcases with ⟨hU,hhead,_hKcore,_hker,_hiso,hlist⟩ | hnatural
  · exact (hseven (source_a5_original_overcomponent_seven_of_shortlist
      D e hn hout ht htn p hLI.le hIX hI hS hU hhead hlist)).elim
  · exact hnatural

end CFSG.Quasithin.Chapter10
