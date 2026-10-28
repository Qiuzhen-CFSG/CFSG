module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.LocalGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.PlaneStabilizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.ThreeFixed

/-!
# Assembling the order-three intersection witness

The four-group V = E ∩ F detects both missing geometric clauses: an element
normalizing E and V normalizes F, and an element of order three normalizing
V has its fixed subgroup on E disjoint from F.

When |N(E)/E| = 168, the seven-plane stabilizer construction supplies such
an actor of order three. Sylow conjugacy inside N(E) gives its fixed subgroup
on E order four. Combining these results constructs the actual intersection
witness without any F-normalizer action or actor-fusion premise.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, p.7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- The geometric assembly from an actual intersection-stabilizing actor
and the order of its fixed subgroup on E. -/
public theorem l27IntersectionWitness_of_intersection_actor
    {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (q : G)
    (hE : q ∈ normalizer (CaseII.E D k : Set G))
    (hV : q ∈ normalizer ((CaseII.E D k ⊓ CaseII.F D k : Subgroup G) : Set G))
    (ho : orderOf q = 3)
    (hfix : Nat.card (CaseII.E D k ⊓ centralizer ({q} : Set G) : Subgroup G) = 4) :
    Nonempty (L27IntersectionWitness D k) :=
  ⟨{ actor := q
     normalizes_E := hE
     normalizes_F := CaseII.l27_normalizes_F_of_normalizes_intersection D k q hE hV
     actor_order := ho
     fixed_card := hfix
     fixed_disjoint := CaseII.l27_intersection_fixed_disjoint D k q hV ho }⟩

/-- The order-168 quotient branch supplies the actual order-three intersection
witness, with no additional fusion or normalizer-action hypothesis. -/
public theorem l27IntersectionWitness_of_168
    {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h168 : Nat.card (CaseII.eNormalizerQuotient D k) = 168) :
    Nonempty (L27IntersectionWitness D k) := by
  obtain ⟨q, hE, hV, ho⟩ := CaseII.l27_exists_intersection_actor D k h168
  exact l27IntersectionWitness_of_intersection_actor D k q hE hV ho
    (CaseII.l27_three_fixed_card D k h168 q hE ho)

end Theory.GroupTheory.HeldM22A10.M22Identification
