module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces

/-!
# The local intersection needed to exclude the order-168 branch

Janko chooses a subgroup Q1 of order three in N(E) intersect N(F). Its
fixed subgroup on E is a four-group disjoint from F. This is the precise
geometric input for the final contradiction in N(F)/F: the fixed four-group
embeds in the quotient and commutes with the nontrivial image of Q1.

This structure records that witness; it has no assumed inhabitant. Its
construction from the order-168 automizer remains a separate proof obligation.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, p.7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- A generator of the source Q1 with its actual fixed subgroup on E. -/
public structure L27IntersectionWitness {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) where
  actor : G
  normalizes_E : actor ∈ normalizer (CaseII.E D k : Set G)
  normalizes_F : actor ∈ normalizer (CaseII.F D k : Set G)
  actor_order : orderOf actor = 3
  fixed_card : Nat.card (CaseII.E D k ⊓ centralizer ({actor} : Set G) : Subgroup G) = 4
  fixed_disjoint : Disjoint (CaseII.E D k ⊓ centralizer ({actor} : Set G)) (CaseII.F D k)

end Theory.GroupTheory.HeldM22A10.M22Identification
