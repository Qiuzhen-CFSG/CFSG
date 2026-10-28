module

public import Theory.GroupTheory.MarkedPerfectCoverAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Covers
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# The special-linear graph action from its marked projective action

The genuine scalar-cover theorem recovers SL3 with the supplied projection
marking. Perfect central-cover uniqueness then identifies its transported
automorphism with inverse transpose. This applies to the new marking
obtained from the actual graph involution in the centralizer quotient.

Source: Aschbacher--Smith F.6.18(11), p.310, and I.1.1--I.1.4, pp.407--408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] {L : Subgroup G}

/-- The new projective marking recovers the exact graph action on the special cover. -/
theorem component_linear_graph_action_of_quotient
    (hL : IsComponent G L) (ho : Odd (Nat.card F))
    (eL : L ⧸ center L ≃* PSL(3,F)) (hz : center L ≠ ⊥)
    (α : MulAut L)
    (hα : ∀ x, eL (QuotientGroup.mk' (center L) (α x)) =
      Matrix.PSL3.OuterSolvable.graph F (eL (QuotientGroup.mk' (center L) x))) :
    ∃ a : L ≃* SL(3,F), ∀ x, a (α x) = Matrix.PSL3.OuterSolvable.graphSL F (a x) := by
  let : IsQuasisimple L := hL.2
  rcases component_linear_three_cover hL ho eL with ⟨h, _⟩ | ⟨_, _, a, ha⟩
  · exact (hz h).elim
  · exact ⟨a.symm, equiv_symm_intertwines_of_marked_cover
      (Matrix.PSL3.projection F) (Matrix.PSL3.projection_ker F).le
      (eL.toMonoidHom.comp (QuotientGroup.mk' (center L))) a ha α
      (Matrix.PSL3.OuterSolvable.graphSL F) (Matrix.PSL3.OuterSolvable.graph F)
      hα (fun _ => rfl)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
