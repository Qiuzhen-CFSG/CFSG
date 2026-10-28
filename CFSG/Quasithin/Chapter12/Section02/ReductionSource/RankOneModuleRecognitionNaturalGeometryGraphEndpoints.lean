module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraphEndpoints
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryGraph

/-!
# The crossed endpoint centralizers on the original reduced layer

Under the contrary abelian assumption, the actual odd critical
configuration has both endpoint closures in the opposite central-line
centralizer. The same ambient conjugator is retained in the closure,
vertex and centralizer statements. This proves the assertion marked (!)
in 6.1.19 with the Chapter 12 E.6.1 and global-s inputs discharged.

The subsequent index-two normalizer, parameter and nonabelianness
arguments remain with qt-d-1222-rankone-recognition-natural, as do the
initial action and final 6.1.27 assembly.
Source: Aschbacher–Smith, 6.1.19, printed pp.673–674.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual odd configuration satisfies both crossed centralizer bounds
from 6.1.19 (!), without extra graph, weak-closure or fusion premises. -/
theorem source_escape_odd_crossed_configuration_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    ∃ d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L),
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
        d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L) ∧
      d.localClosure ≤ (d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj d.representative).toMonoidHom := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  exact ⟨d,d.crossed_centralization h611 hnatural
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
