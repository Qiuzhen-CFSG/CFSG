module
public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.A5Point
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries

/-!
# The original A₅ abelian closures without an escape premise

Positive recognition of a nonabelian point closure contradicts the two
source model exclusions. All local closures are then abelian by inclusion
of conjugators. The full closure is an elementary abelian normal subgroup
of the literal point centralizer, placing V in its two-core.

The final theorem gives exactly the centralizerConjugateClosure used by
the Section 13.6 terminal setup, retaining the original generator of V₁.
Construction of the marked Context remains earlier preparation.
Source: Aschbacher–Smith, 13.5.12 and 13.6.2, printed pp.918 and926.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.SourceAssembly
open A5Source Section06.CentralizerReduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- Original 13.6.2 for the full point centralizer. -/
theorem a5_point_closure_abelian (hcounter : IsA5Counterexample G) :
    IsMulCommutative (conjugateSpanBy V (centralizer (V₁ : Set G))) := by
  by_contra hV
  rcases source_point_full_modelConclusion d hV with ⟨_,h⟩ | ⟨hn,_⟩
  · exact h.elim hcounter.1 hcounter.2
  · omega

/-- Every local point-centralizer closure is abelian. -/
theorem a5_all_point_closures_abelian (hcounter : IsA5Counterexample G)
    (H : Subgroup G) (hH : H ≤ centralizer (V₁ : Set G)) :
    IsMulCommutative (conjugateSpanBy V H) := by
  let := a5_point_closure_abelian d hcounter
  exact conjugateSpanBy_isMulCommutative_of_le le_rfl hH

/-- The original module lies in the literal point-centralizer two-core. -/
theorem a5_module_le_point_core (hcounter : IsA5Counterexample G) :
    V ≤ (centralizer (V₁ : Set G)).pCoreIn 2 := by
  let C := centralizer (V₁ : Set G)
  let := d.elementary
  let := a5_point_closure_abelian d hcounter
  have hel : IsElementaryAbelian 2 (conjugateSpanBy V C) :=
    conjugateSpanBy_elementary_of_commutative V C
  have hVC : V ≤ C :=
    (le_centralizer V).trans (centralizer_le (d.flag.one_le_two.trans d.flag.two_le_V))
  exact (le_conjugateSpanBy V C).trans
    (le_pCoreIn_of_normalizes hel.isPGroup (conjugateSpanBy_le hVC C.le_normalizer)
      (le_normalizer_conjugateSpanBy V C))

/-- The abelian-closure premise of the original terminal A₅ setup. -/
theorem a5_centralizerConjugateClosure_abelian
    (hcounter : IsA5Counterexample G) (z : G) (hz : zpowers z = V₁) :
    IsMulCommutative (centralizerConjugateClosure V z) := by
  rw [centralizerConjugateClosure_eq_conjugateSpanBy]
  have hc : centralizer (V₁ : Set G) = centralizer ({z} : Set G) := by
    rw [←hz,zpowers_eq_closure,centralizer_closure]
  rw [←hc]
  exact a5_point_closure_abelian d hcounter
end CFSG.Quasithin.Chapter13.Section05.SourceAssembly
