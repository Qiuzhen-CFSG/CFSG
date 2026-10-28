module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionNormalizer

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosure

/-!
# The escaping normalizer and G.2 comparison on the Chapter 12 layer

The existing 6.1.9(2) theorem supplies the Sylow-centralizer normalizer bound.
The unrestricted Frattini argument therefore gives the actual 6.1.9(5)
factorization even when the centralizer escapes M. The natural marking
supplies E.6.1, identifying the normalizer closure with the original U and
matching the G.2 generated group, two-core and intersection with L₁, R and E.

No contained-centralizer hypothesis or local normalizer callback remains.
The initial natural marking and the remaining G.2 and escaping geometry
are still obligations of qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith, 6.1.9(5) and 6.1.21, printed pp.669, 675–676.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual source 6.1.9(5) factorization, including the escaping branch.
The original 6.1.9(2) normalizer theorem supplies its only local premise. -/
theorem source_central_line_factorization
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    CentralLineNormalizerFactorization (normalizer (L : Set G))
      (ZS (T : Subgroup G) L (wholeReduced T L)) :=
  central_line_factorization_of_S_normalizer h611
    (source_central_line_S_normalizer_le D h h611)

/-- On the original Chapter 12 module, the full central-line normalizer
and its pointwise centralizer have exactly the same conjugate closure. -/
theorem source_escape_normalizer_span
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n) :
    conjugateSpanBy (commutatorLayer T L) (Escape.H (T : Subgroup G) L (wholeReduced T L)) =
      Escape.U (T : Subgroup G) L (wholeReduced T L) :=
  natural_escape_normalizer_span h611
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611)

/-- The G.2 constructions used by 6.1.21 are the literal original closure,
generated group, two-core and intersection. No contained-centralizer premise
is needed, so these comparisons apply in the escaping branch. -/
theorem source_escape_G2_constructions
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (l : G) :
    let E := naturalEscapeSetup (T : Subgroup G) L (wholeReduced T L)
    E.U = Escape.U (T : Subgroup G) L (wholeReduced T L) ∧
      E.I l = Escape.L1 (T : Subgroup G) L (wholeReduced T L) l ∧
      E.S l = Escape.R (T : Subgroup G) L (wholeReduced T L) l ∧
      E.S₂ l = Escape.E (T : Subgroup G) L (wholeReduced T L) l :=
  natural_escape_G2_constructions h611
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) l

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
