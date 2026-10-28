module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryHyperplanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryLine

/-!
# The odd critical parameter on the original reduced layer

The chosen module supplies E.6.1, global s=n and the central-line
normalizer bound. The actual odd configuration therefore forces n=2
and an order-two intersection of its distinct endpoint lines. Under
the contrary abelian assumption the moving natural neighbor meets the
full escaping closure in precisely its endpoint line, while escaping
the local two-core. In particular the n>2 escaping closure is nonabelian.

The remaining n=2 transvection argument, initial natural action and
Sylow-centralizer proof, and final source 6.1.27 assembly remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19–20, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The odd critical geometry forces n=2 and the actual common involution
line, with the Chapter 12 rank and normalizer premises discharged. -/
theorem source_escape_odd_parameter_and_intersection
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L)) :
    n = 2 ∧ Nat.card (ZS (T : Subgroup G) L (wholeReduced T L) ⊓
      (ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj d.representative).toMonoidHom : Subgroup G) = 2 :=
  d.parameter_and_intersection h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611)

/-- An abelian escaping closure can occur only at parameter two. -/
theorem source_escape_parameter_two_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) : n = 2 := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  exact (source_escape_odd_parameter_and_intersection D h h611 hnatural d).1

/-- Source 6.1.20(2) for every parameter greater than two. -/
theorem source_escape_nonabelian_of_parameter_gt_two
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hn : 2 < n) :
    ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G) := by
  intro hab
  have he := source_escape_parameter_two_of_abelian D h h611 hnatural hI hab
  omega

/-- The order-two common line and the exact moving-neighbor intersection
with the full abelian closure, using the same ambient conjugators. -/
theorem source_escape_neighbor_intersection_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧
    ∃ d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L),
      let Z := ZS (T : Subgroup G) L (wholeReduced T L)
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      Nat.card (Z ⊓ Z' : Subgroup G) = 2 ∧
      ∃ a : G, let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
        E ≤ Escape.I (T : Subgroup G) L (wholeReduced T L) ∧
        ¬ E ≤ d.H.pCoreIn 2 ∧
        E ⊓ Escape.U (T : Subgroup G) L (wholeReduced T L) = Z' := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  obtain ⟨hn,hline⟩ := source_escape_odd_parameter_and_intersection D h h611 hnatural d
  exact ⟨hn,d,hline,d.exists_neighbor_with_closure_intersection h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
