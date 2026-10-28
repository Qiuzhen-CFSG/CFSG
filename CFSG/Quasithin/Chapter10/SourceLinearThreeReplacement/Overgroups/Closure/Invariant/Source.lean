module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Automizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Models
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Assembly

/-!
# The invariant wreath-action sieve in source 10.2.4

The literal S₃ wreath C₂ quotient identifies Aut_T(P) with D₈. This excludes
both linear-three covers and M₁₁ by their actual Sylow-pair automizers, and
excludes the symplectic row because its automizer is cyclic. The surviving
binary models force an outer actor by their inner-pair invariant. The proved
inner/graph coverage and exact two-core kernel then identify IT/O₂(IT)
with the full automorphism group of the stated projective matrix carrier.

All Sylow restrictions come from the original ambient Sylow T. The source
normal-closure consumer below uses this sieve on its invariant branch;
the independent Held alternative remains in that consumer's conclusion.

Source: Aschbacher--Smith, 10.2.4, printed p.747, using 1.3.4, pp.509--511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The exact invariant sieve, with the original local and wreath inputs. -/
theorem invariantWreathSieve (T : Sylow 2 G) : InvariantWreathSieveAt T := by
  intro X P H I h _ hI _ hn hi _ hX _ hw ha
  exact Invariant.models_of_dihedral h hI.1 hn hi hX
    (Invariant.automizer_equiv_dihedral h ha.1 hw) ha

/-- Apply the completed sieve to the actual component-orbit normal closure.
Only the independent parabolic recognition remains outside this implication. -/
theorem normalClosure_models {T : Sylow 2 G} {X P H : Subgroup G}
    (h : LocalInput 3 (T : Subgroup G) X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hw : Nonempty (XiQuotient (X ⊔ (T : Subgroup G)) ≃* ParabolicWreath)) :
    conjugateSpanBy X H = X ∨ ∃ I : Subgroup G,
      I ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient I) ∧
      conjugateSpanBy X H = componentOrbit I (T : Subgroup G) ∧ ClosureModel T I :=
  normalClosure_models_of_sieve (invariantWreathSieve T) h hH hw

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
