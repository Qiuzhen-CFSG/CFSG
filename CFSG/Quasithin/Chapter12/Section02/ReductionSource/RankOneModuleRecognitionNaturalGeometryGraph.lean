module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryCoreAction

/-!
# Critical-distance branches on the original Chapter 12 layer

The chosen module supplies E.6.1, the exact global-s value and the
central-line normalizer bound. An even critical pair therefore proves that
the literal closure U is nonabelian. If U were abelian, the source instead
constructs a minimal H-star vertex in IT, its elementary closure, and an
odd critical endpoint at distance at least three.

The final application carries the even branch into the existing nontrivial
elementary core action on U/Z_S. The odd case of 6.1.19, the initial action
and the subsequent component analysis remain with the final assembly owner
qt-d-1222-rankone-recognition-natural; this is not unconditional 6.1.27.

Source: Aschbacher–Smith, 6.1.16–20, printed pp.672–675, and the
component setup of 6.1.24, printed pp.676–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
open ChapterF.Section07.Track
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- An even critical distance proves nonabelianness on the whole reduced layer. -/
theorem source_escape_nonabelian_of_even_track
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    {H : Subgroup G}
    (d : SourceSetup (fun i => if i then H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)
      else (L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)))
    (hne : d.V ≠ ⊥)
    (hseed : d.seed.map ((L ⊔ (T : Subgroup G)) ⊔ H).subtype = commutatorLayer T L)
    (heven : Even (d.track hne)) :
    ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  NaturalEscapeGraph.nonabelian_of_even_track h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) d hne hseed heven

/-- The contrary abelian assumption constructs the actual odd source configuration. -/
theorem source_escape_odd_configuration_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    Nonempty (NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L)) :=
  NaturalEscapeGraph.odd_configuration_of_abelian h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hI hab

/-- The component argument has its nontrivial elementary core image unless
the genuine odd-distance configuration of 6.1.19 occurs. No nonabelianness
or independently supplied coset-graph premise is required. -/
theorem source_escape_core_action_or_odd_configuration
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G)) :
    letI := h611.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)
    (pCore 2 a.range = ⊥ ∧
      ((normalizer (L : Set G)).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a < a.range ∧
      ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L) ∧
        Escape.E (T : Subgroup G) L (wholeReduced T L) l <
          Escape.R (T : Subgroup G) L (wholeReduced T L) l ∧
        IsElementaryAbelian 2
          (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
            (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a) ∧
        ((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
          (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a ≠ ⊥) ∨
      Nonempty (NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L)) := by
  let := h611.ZS_normal_in_escape_U
  rcases NaturalEscapeGraph.nonabelian_or_odd_configuration h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hI with hnon | hodd
  · exact Or.inl (source_escape_core_action_setup D h h611 hnatural hnon hI)
  · exact Or.inr hodd

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
