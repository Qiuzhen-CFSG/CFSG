module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.SchreierData

/-!+# The finite checks used by the max4 Schreier reduction

The table respects inverse columns and all seven original source loops.
The selected tree edges freely reduce to the empty word. These finite checks
are isolated from the structural lifting proof so its elaboration does not
repeat the kernel computations.

Source: the literal seven max4 words; see `source/README.md`.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.TableChecks
open Subgroup.CosetWordCertificate

theorem step_inverse : ∀ (i : Vertex) (a : Bool),
    step (step i (a, false)) (a, true) = i := by decide +kernel

set_option maxRecDepth 10000 in
theorem source_loop : ∀ (i : Vertex) (r : Fin 7),
    endpoint i (sourceWord r) = i := by decide +kernel

set_option maxRecDepth 10000 in
theorem tree_reduces : ∀ k : Fin 167, reduce (edgeWord (treeEdge k)) = [] :=
  by decide +kernel

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.TableChecks
