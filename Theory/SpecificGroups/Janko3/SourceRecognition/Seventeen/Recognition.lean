module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PointIntersection
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairIntersection
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Alignment
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Completion

/-!
# Baumeister Corollary 2.10: the marked PSL₂(16):2 completion

The genuine matrix extension by fourth-power Frobenius now supplies all
three local groups, all three literal intersections, generation and the
self-centralizing point two-core. Applying simultaneous embedding uniqueness
to this constructed model identifies every faithful source completion with
PSL₂(16):2. A prescribed overlap involution can be carried to the specified
fourth-power field involution. There is no recognition or model-amalgam premise.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
Corollary 2.10 and its preceding model construction.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen
namespace ModelAmalgam

/-- The actual model amalgam in the source, with every clause discharged. -/
def source : SourceData Model where
  H1 := point
  H2 := pair
  H3 := Triangle
  generated := generated
  action := pointAction
  pointEquiv := pointEquiv
  core_centralizer := core_centralizer
  pairEquiv := pairEquiv
  triangleEquiv := triangleEquiv
  overlap12 := overlapEquiv
  overlap13 := overlap13
  overlap23 := overlap23

end ModelAmalgam
namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

/-- Corollary 2.10, with the two source stabilizers preserved. -/
theorem corollary_2_10 :
    ∃ e : G ≃* Model, S.H1.map e.toMonoidHom = ModelAmalgam.point ∧
      S.H2.map e.toMonoidHom = ModelAmalgam.pair :=
  S.completions_marked_equiv ModelAmalgam.source

/-- The chosen involution is the actual fourth-power field actor. -/
theorem corollary_2_10_marked (s : G) (hs : s ∈ S.H1 ⊓ S.H2) (hos : orderOf s = 2) :
    ∃ e : G ≃* Model, S.H1.map e.toMonoidHom = ModelAmalgam.point ∧
      S.H2.map e.toMonoidHom = ModelAmalgam.pair ∧ e s = involution :=
  S.completions_equiv_preserving_involution ModelAmalgam.source s hs hos
    involution ModelAmalgam.involution_mem_overlap involution_order

end SourceData
namespace CompletionData
variable {G : Type*} [Group G] (C : CompletionData G)

/-- Every faithful three-group completion, hence the universal completion of
Corollary 2.8, is the genuine fourth-power-Frobenius extension. -/
theorem corollary_2_10 :
    ∃ e : G ≃* Model, C.H1.map e.toMonoidHom = ModelAmalgam.point ∧
      C.H2.map e.toMonoidHom = ModelAmalgam.pair :=
  C.source.corollary_2_10

end CompletionData
end Sporadic.Janko3.SourceRecognition.Seventeen
