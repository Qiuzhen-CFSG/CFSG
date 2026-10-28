module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryDefs

/-!
# Applying the field-action contradiction to the Chapter 12 layer

The first theorem supplies the published FieldConjugateEscape interface on
B = [R₂(LT),L], and the second uses it in the original conjugate-centralization
consumer. The original 4.3.1 argument supplies normalizer control. The
solvable action and field local-module construction remain explicit inputs;
this does not assert that source 6.1.14(5) has already been proved.

Source: Aschbacher--Smith, 6.1.14(5)--15 and 12.2.2(3d).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Apply the terminal field contradiction on the original reduced layer,
discharging normalizer control by the proved source 6.1.9 factorization. -/
theorem source_fieldConjugateEscape_of_local_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hsolv : Group.IsSolvable (normalizerAction (normalizer (L : Set G))
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))).range)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n) :
    FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n := by
  apply fieldConjugateEscape_of_naturalLocalAction _ _ _ _ _ _ hsolv hloc
  intro hI d hd
  obtain ⟨c, hc, m, hm, rfl⟩ :=
    source_central_line_normalizer_factorization D h h611 hI d hd
  exact mul_mem (hI hc) hm.1

/-- Actual consumer of the constructed field escape. The other source
families are the independent corank, fusion and fixed-space producers. -/
theorem source_high_conjugate_centralizes_of_local_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L))
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hcorank : ConjugateCorankFormula (T : Subgroup G) (commutatorLayer T L) n)
    (hfusion : MutualConjugateFusion (T : Subgroup G) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)))
    (hfixed : FixedSpaceAlternatives L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hsolv : Group.IsSolvable (normalizerAction (normalizer (L : Set G))
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))).range)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  source_high_conjugate_centralizes_of_source_inputs h611 hnatural hE hr hI
    hcorank hfusion hfixed
    (source_fieldConjugateEscape_of_local_action D h h611 hsolv hloc) hn g hg

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
