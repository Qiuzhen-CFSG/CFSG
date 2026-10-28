module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalInitial

/-!
# The escaping reduced quotient on the original Chapter 12 layer

The natural action constructs the two-core containment and reduced quotient
for the actual U generated from [R₂(LT),L]. In particular U/Z_S is elementary,
so the terminal contradiction now needs only its order bound and the marked
PSL₂ prime component. No separate commutator or elementary-quotient premise
is required. The completed contained branch supplies n = 2 after escape is
excluded, preserving both literal weak-closure alternatives.

The final theorem also applies the checked fixed-kernel argument. The earlier
6.1.4–5 inputs and the escaping order/component constructions remain explicit
obligations of qt-d-1222-rankone-recognition-natural; this module does not assert
the unconditional source_natural_reduction_of_many.

Source: Aschbacher–Smith, 6.1.17(1–2), 6.1.20(1), and 6.1.27, pp.672–679.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original escaping closure has a reduced image in I/Z_S, lies in T,
and has all its commutators in Z_S. -/
theorem source_escape_reduced_core
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n) :
    letI := natural_escape_central_line_normal (T := T) (L := L) (V := wholeReduced T L)
    IsPReduced 2 (((Escape.U (T : Subgroup G) L (wholeReduced T L)).subgroupOf
      (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
        (QuotientGroup.mk' ((ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf
          (Escape.I (T : Subgroup G) L (wholeReduced T L))))) ∧
    Escape.U (T : Subgroup G) L (wholeReduced T L) ≤ T ∧
    ⁅Escape.U (T : Subgroup G) L (wholeReduced T L),
      Escape.U (T : Subgroup G) L (wholeReduced T L)⁆ ≤
        ZS (T : Subgroup G) L (wholeReduced T L) :=
  ⟨(natural_escape_reduced_core h611 hnatural).1,
    natural_escape_U_le_sylow h611 hnatural, natural_escape_commutator h611 hnatural⟩

/-- Apply the constructed elementary quotient to the actual Chapter 12
reduction. Only the escaping order bound and actual prime image remain. -/
theorem source_natural_reduction_of_natural_and_escape_order
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hsize : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256)
    (hprime : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      NaturalEscape.PrimeComponent (T : Subgroup G) L (wholeReduced T L)) :
    Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  let := h611.ZS_normal_in_escape_U
  have hI : centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G) := by
    by_contra he
    exact NaturalEscape.false_of_small_quotient (hsize he)
      (natural_escape_quotient_elementary h611 hnatural) (hprime he)
  obtain ⟨hn, hw⟩ := source_contained_natural D h h611 hnatural hout hI
  refine ⟨hn, hn ▸ hnatural, hCT, hI, ?_⟩
  rcases hw with hz | ho
  · exact Or.inl hz
  · exact Or.inr fun hw => ho ((le_C_iff h611.ZS_le_T 1).mpr hw)

/-- The initial fixed-kernel proof and contained branch are supplied. The
6.1.4–5 inputs and escaping order/component constructions remain with this task. -/
theorem source_natural_reduction_of_earlier_sources_and_escape_order
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hquot : IsNaturalFixedQuotient L (commutatorLayer T L) n)
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hsize : letI := h611.ZS_normal_in_escape_U
      IsNaturalModule L (commutatorLayer T L) n →
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ →
      ¬ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256)
    (hprime : letI := h611.ZS_normal_in_escape_U
      IsNaturalModule L (commutatorLayer T L) n →
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ →
      ¬ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      NaturalEscape.PrimeComponent (T : Subgroup G) L (wholeReduced T L)) :
    Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  obtain ⟨hnatural, hCT⟩ := source_initial_natural_of_earlier_sources h611 hout hquot hcentral
  exact source_natural_reduction_of_natural_and_escape_order D h h611 hnatural hCT hout
    (hsize hnatural hCT) (hprime hnatural hCT)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
