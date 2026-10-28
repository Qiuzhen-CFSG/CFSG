module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalInitial
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContained

/-!
# The initial natural reduction on the whole Chapter 12 layer

The fixed-quotient model and H-star centralization conclusions of 6.1.4–5
give the full natural action and trivial Sylow centralizer on [R₂(LT),L].
Irreducibility then identifies every original chosen subgroup with this
whole layer. The final application supplies the initial and the completed
contained branches to the literal 6.1.27 consumer.

The earlier 6.1.4–5 source statements and escaping geometry remain explicit;
their proofs belong to qt-d-1222-rankone-recognition-natural. In particular
this module does not assert `source_natural_reduction_of_many`.

Source: Aschbacher–Smith, 6.1.4–6 and 6.1.27, pp.664–669 and 679.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Apply the fixed-kernel removal to the original whole reduced subgroup. -/
theorem source_initial_natural_of_earlier_sources
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hquot : Chapter6.Source.IsNaturalFixedQuotient L (commutatorLayer T L) n)
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ :=
  h611.initial_natural_of_earlier_sources hout hquot hcentral

omit [Finite G] in
/-- The chosen Irr-plus subgroup fills the whole natural commutator layer. -/
theorem chosen_eq_layer_of_natural (D : ChosenModule T L V)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    V = commutatorLayer T L :=
  (hnatural.invariant_subgroup V D.le_rankOne_commutatorLayer D.normalizes).resolve_left
    D.ne_bot

/-- The same original quotient acts naturally on the chosen subgroup;
the equality with the whole layer is proved by irreducibility. -/
theorem source_chosen_natural_of_earlier_sources (D : ChosenModule T L V)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hquot : Chapter6.Source.IsNaturalFixedQuotient L (commutatorLayer T L) n)
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    V = commutatorLayer T L ∧ Chapter6.Source.IsNaturalModule L V n := by
  have hnatural := (source_initial_natural_of_earlier_sources h611 hout hquot hcentral).1
  have heq := chosen_eq_layer_of_natural D hnatural
  exact ⟨heq, heq ▸ hnatural⟩

/-- The actual 6.1.27 consumer with initial fixed-kernel removal and the
contained branch discharged. The two earlier source statements and escape
geometry remain obligations of this task's final assembly. -/
theorem source_natural_reduction_of_earlier_initial_sources
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hquot : Chapter6.Source.IsNaturalFixedQuotient L (commutatorLayer T L) n)
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hescape : letI := h611.ZS_normal_in_escape_U
      Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n →
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ →
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Chapter6.Source.RankOneRecognition.EscapingAlternative
        (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n := by
  obtain ⟨hnatural, hCT⟩ := source_initial_natural_of_earlier_sources h611 hout hquot hcentral
  exact source_natural_reduction_of_contained_branch D h h611 hnatural hCT hout
    (hescape hnatural hCT)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
