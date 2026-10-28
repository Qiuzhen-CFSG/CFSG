module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedReduction

/-!
# The contained-centralizer reduction on the Chapter 12 layer

Nonsolvable uniqueness supplies the unique maximal two-local over LT.
The Chapter 6 weak-closure reduction therefore applies to the actual layer
[R₂(LT),L], giving a noncentralizing conjugate when N_G(W₀) escapes.

The conditional assembly below retains exactly the weak-closure bounds
of 6.1.12 and the high-parameter conjugate geometry from 6.1.10--14.
Its application to the original natural-reduction consumer retains those
inputs and the independent escaping-centralizer branch. No assertion of
the unconditional source 6.1.15 or 6.1.27 is made here.

Source: Aschbacher--Smith, 6.1.15, printed p.672, and the application
of 6.1.27 in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

private theorem local_unique (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  simpa only [he] using hu.normalizer_unique

/-- The first reduction in 6.1.15, on the original whole reduced layer.
The conjugating element lies outside M, since M-conjugates centralize the
layer. The source uniqueness premise is fully discharged. -/
theorem source_noncentralizing_conjugate_of_normalizer_escape
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hescape : ¬ normalizer
      (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G)) :
    ∃ g : G, g ∉ normalizer (L : Set G) ∧
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
        centralizer (commutatorLayer T L : Set G) := by
  obtain ⟨g, hgT, hg⟩ :=
    Chapter6.Source.RankOneRecognition.exists_noncentralizing_conjugate_of_normalizer_escape
      h611 hnatural (local_unique D h) hescape
  exact ⟨g, fun hgM => hg
    (Chapter6.Source.RankOneRecognition.M_conjugate_layer_centralizes h611 hnatural hgM),
    hgT, hg⟩

/-- Conditional contained-branch assembly. The two explicit geometric
inputs still need their earlier-source producers. -/
theorem source_contained_natural_of_weak_closure_and_conjugate_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hsplit : ¬ normalizer
        (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
          normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G))
    (hhigh : 2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1)
    (hconj : 2 < n → ∀ g : G,
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
        centralizer (commutatorLayer T L : Set G)) :
    Chapter6.Source.RankOneRecognition.ContainedAlternative (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  Chapter6.Source.RankOneRecognition.containedAlternative_of_weak_closure_and_conjugate_geometry
    h611 hnatural (local_unique D h) hI hsplit hhigh hconj

/-- Apply the new contained reduction to the existing natural-reduction
consumer. The independent escaping branch and the two earlier-source
geometric inputs remain explicit. -/
theorem source_natural_reduction_of_contained_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hsplit : ¬ normalizer
        (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
          normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G))
    (hhigh : 2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1)
    (hconj : centralizer
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
          normalizer (L : Set G) →
      2 < n → ∀ g : G,
        (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
          centralizer (commutatorLayer T L : Set G))
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Chapter6.Source.RankOneRecognition.EscapingAlternative
        (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_natural_reduction_of_source_branches h611 hnatural hCT
    (fun hI => source_contained_natural_of_weak_closure_and_conjugate_geometry
      D h h611 hnatural hI hsplit hhigh (hconj hI)) hescape

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
