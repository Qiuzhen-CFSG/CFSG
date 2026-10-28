module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.Ordering
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableCompletion.Centralizer

/-!
# Original empty-family hypotheses through source 15.4.11(2)

The actual multiple-overgroup branch constructs Hypothesis 15.4.1. The
complete preceding source implications then prove C_G(Ω₁(Z(T))) = T,
solvability of every maximal local overgroup, and both the core-centralizer
and ordering conclusions of 15.4.11. No Chapter 15 intermediate conclusion
is assumed. The remaining universal A/C, 3.1.1, D.1.4–5 and solvable E.2.9
inputs are the original earlier statements used by the ratio proof.

The Thompson noncentrality assertion 15.4.11(3), the exceptional source
15.4.7, and construction of Y remain separate source obligations. This
module does not use the legacy Chapter 14 empty-family certificates.
Source: Aschbacher–Smith, pp.1155–1161 and the split in 15.4.25, p.1165.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open MaximalPrimeSource FamilySource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine source hypothesis is constructed from the cardinality version
used by the final centralizer-overgroup split. -/
theorem sourceHypotheses (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    SourceHypotheses T := by
  obtain ⟨M, hM, N, hN, hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
  exact ⟨hG, hempty, M, N, hM.1, hN.1, hM.2, hN.2, hne⟩

variable
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})

include hA hC h311 hD15 hD14 h29

/-- Source 15.4.8 directly from the original simple-QTKE and empty-family
hypotheses, retaining only genuine earlier universal results. -/
theorem source_centralizer_eq_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T := by
  obtain ⟨h42, h44⟩ := RatioSource.source_lemma_15_4_2_of_D1_E2 hA hC h311 hD15 hD14 h29
  exact CentralizerWitness.C26FreeSource.source_lemma_15_4_8 T
    (sourceHypotheses hG T hempty hmany) h42 h44

/-- The literal preparation for constructing Y, simultaneously for every
maximal two-local overgroup of T. The centralizer and local ordering facts
are constructed, rather than fields assumed in a local input record. -/
theorem source_local_preparation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T ∧
    (∀ M ∈ maximalLocals T, Group.IsSolvable M ∧
      M ⊓ centralizer (localV T M : Set G) = M.pCoreIn 2 ∧ IsOrderingMaximal T M) ∧
    ¬ ∃! M : Subgroup G, IsOrderingMaximal T M := by
  obtain ⟨h42, h44⟩ := RatioSource.source_lemma_15_4_2_of_D1_E2 hA hC h311 hD15 hD14 h29
  have h := sourceHypotheses hG T hempty hmany
  have hcentral := CentralizerWitness.C26FreeSource.source_lemma_15_4_8 T h h42 h44
  refine ⟨hcentral, ?_, not_unique_ordering_maximal T hcentral hmany⟩
  intro M hM
  exact ⟨(h42 T h).solvable M hM.1 hM.2,
    localV_centralizer T M hM.2 hcentral, ordering_maximal T hcentral hM⟩

/-- The opening B.2.16 application in 15.4.12, on the original source groups.
Only the separate 15.4.11(3) noncentrality conclusion remains as a local
input; the centralizer equality, solvability and rank bound are constructed. -/
theorem source_exceptional
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (M : Subgroup G) (hM : M ∈ maximalLocals T)
    (hmoved : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥) :
    ∃ hE : IsElementaryAbelian 2
      (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hM.2)),
      ∃ d : @Chapter1.RadicalNormalizers.ThompsonSource.Exceptional M _
        (T.subtype hM.2) hE, d.count = 1 ∨ d.count = 2 := by
  obtain ⟨hc, hlocals, _⟩ := source_local_preparation hA hC h311 hD15 hD14 h29
    hG T hempty hmany
  exact FamilySource.ThompsonSource.exceptional hB hG T M hM.1 hM.2
    (hlocals M hM).1 hc hmoved

end CFSG.Quasithin.Chapter15.Section04.InitialSource
