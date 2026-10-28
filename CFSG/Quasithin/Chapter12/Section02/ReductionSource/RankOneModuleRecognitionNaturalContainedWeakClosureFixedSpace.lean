module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpace

/-!
# Natural A₂ control on the whole Chapter 12 layer

The Chapter 6 fixed-space argument applies to the literal whole reduced
subgroup and its commutator layer. It requires only the supplied natural
marking and Hypothesis 6.1.1; the other standing Chapter 12 assumptions are
not needed for this local consequence. In particular the original actor
need not be elementary, and no contained-centralizer premise is required.

The final application gives all three weak-closure conclusions while retaining
s(G,B)=n for its independent producer. It does not assert the rank formula.
Source: Aschbacher--Smith, 6.1.12, pp.669--670, in the 12.2.2 setup, p.795.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- The exact local A₂ control for B = [R₂(LT),L], independent of s(G,B). -/
theorem source_natural_fixedSpace_control
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    letI := h611.layer_elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      ChapterE.inducedAutomizer (commutatorLayer T L) A ∈
        ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation (commutatorLayer T L)) 2 →
      A ≤ centralizer
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  Chapter6.Source.RankOneRecognition.natural_fixedSpace_control h611 hnatural

/-- The local control discharges both containment premises of source 6.1.12.
The independent rank equality is the only extra numerical input. -/
theorem source_natural_weak_closure_bounds_of_globalS_eq
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n) :
    (2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1) ∧
      Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer
          (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  Chapter6.Source.RankOneRecognition.weak_closure_bounds_of_fixedSpace_control
    h611 hs (source_natural_fixedSpace_control h611 hnatural)

/-- The original weak-closure application with A₂ control fully discharged.
The parent assembly supplies the separately proved rank equality. -/
theorem source_natural_weak_closure_of_globalS_eq
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n) :
    (¬ normalizer (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G)) ∧
    (2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1) ∧
    Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  source_weak_closure_of_rank_and_fixedSpace_control h611 hout hs
    (source_natural_fixedSpace_control h611 hnatural)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
