module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts

/-!
# The intersection actor in Janko's three-fusion argument

The second type of cyclic three-subgroup in N(E) is represented by an
element of N(E) intersect N(F) acting without nonidentity fixed points on E.
These fields specify the actual ambient element and its conjugation action.
Constructing this witness is a separate geometric obligation; the structure
has no assumed inhabitant and contains no fusion or Sylow conclusion.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed p.8, the paragraph preceding Lemma 8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- The source Q* generator, with its actual normalizer memberships and action. -/
public structure FusedNineIntersectionActor {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) where
  actor : G
  normalizes_E : actor ∈ normalizer (CaseII.E D k : Set G)
  normalizes_F : actor ∈ normalizer (CaseII.F D k : Set G)
  actor_order : orderOf actor = 3
  fixed_point_free : ∀ e ∈ CaseII.E D k, Commute actor e → e = 1

end Theory.GroupTheory.HeldM22A10.M22Identification
