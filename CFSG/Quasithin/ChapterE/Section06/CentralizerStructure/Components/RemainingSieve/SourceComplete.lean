module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceTwoMathieuRows
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.M22
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.M23
/-!
# The complete adequate E.6.8 source theorem

The actual 1.1.5 model and marked involution dispatch through the completed
Lie, alternating, odd-linear and sporadic source proofs. All nine excluded
sporadic rows use the original component and its literal two-core quotient.
The genuine earlier 1.2 and E.6.7 producers are supplied internally.

The Borel, symplectic and alternating alternatives retain their full source
fields. The adequate linear-four and odd alternatives omit the unsupported
fixed-space equality for arbitrary members of Γ; the minimal and hyperplane
consumers prove the equality when needed. No model, row, local-subgroup,
module-action or earlier-classification callback remains.
Source: Aschbacher–Smith E.6.8, printed pp.247–248 (`refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

theorem adequateComponentAlternatives_knownSimple
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    AdequateComponentAlternatives M V U (sylowCentralizer (T : Subgroup G) V) L := by
  apply adequateComponentAlternatives_of_two_mathieu_exclusions h ?_ hU hL
  intro A hA X hX hn z hz hne α hα name hm ha hx
  rcases hx with rfl | rfl
  · exact Sporadic.m22_excluded h (e67Input_knownSimple h) hA hX hz α hα ha hm.some
  · exact Sporadic.m23_excluded h (e67Input_knownSimple h) hA hX hz α hα ha hm.some
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
