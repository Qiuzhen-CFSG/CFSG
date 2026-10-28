module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldComponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryLines

/-!+# The contained-centralizer branch on the original Chapter 12 layer

Relative normality of O²(N_L(U)) supplies its actual natural action on the
quadratic conjugate line. Solvability of the central-line normalizer action
then excludes the field-fixed-space case. Together with conjugate corank,
fusion and the exact natural-layer ranks, this proves the high-parameter
centralization and weak-closure alternative of source 6.1.15.

The final application supplies the contained branch to the existing 6.1.27
consumer. The initial natural action and the independent escaping branch
remain with its assembly owner, qt-d-1222-rankone-recognition-natural.
There are no local geometry or rank premises left in the contained branch.

Source: Aschbacher–Smith, 6.1.10–15, printed pp.670–672.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The field residual has the required natural action on the actual
conjugate line; all relative-normality and closure premises are discharged. -/
theorem source_fieldNaturalLocalAction
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n :=
  source_fieldNaturalLocalAction_of_residual_normality D h h611 hnatural
    (fun hn _ hUne hfield => source_field_residual_normal D h h611 hnatural hfield hUne hn)

/-- The involutory-field conjugate escape, with its local-action construction supplied. -/
theorem source_fieldConjugateEscape
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n :=
  source_fieldConjugateEscape_of_fieldNaturalLocalAction D h h611 hnatural
    (source_fieldNaturalLocalAction D h h611 hnatural)

/-- For n > 2, every conjugate of the natural layer contained in T
centralizes that layer when C_G(Z_S) is contained in M. -/
theorem source_high_conjugate_centralizes
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  source_high_conjugate_centralizes_of_field_action D h h611 hnatural
    (source_fieldNaturalLocalAction D h h611 hnatural) hI hn g hg

/-- The contained-centralizer conclusion of source 6.1.15, retaining the
literal normalizer of W₀ and the literal C₁. -/
theorem source_contained_natural
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_contained_natural_of_field_action D h h611 hnatural hout
    (source_fieldNaturalLocalAction D h h611 hnatural) hI

/-- The exact Chapter 12 many-overgroups contract for the contained branch.
Its natural marking and C_T(L)=1 are the independent initial-action inputs. -/
theorem source_contained_natural_of_many
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L
      (Chapter6.Source.layer L (wholeReduced T L)) n)
    (_hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_contained_natural D h.toHypothesis1221 h611 hnatural hout hI

/-- Actual application to the 6.1.27 consumer. Only the independent
escaping-centralizer branch remains with the natural-reduction assembly owner. -/
theorem source_natural_reduction_of_contained_branch
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      EscapingAlternative (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_natural_reduction_of_source_branches h611 hnatural hCT
    (source_contained_natural D h h611 hnatural hout) hescape

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
