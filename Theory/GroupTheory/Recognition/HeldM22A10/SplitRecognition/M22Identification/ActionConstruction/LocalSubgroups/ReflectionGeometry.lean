module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Basic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.FourObstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Choice
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.IntermediateSubgroups
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.YCensus

/-!
# Janko's reflection, conjugate intersection and order-96 subgroup

For every common order-three actor, the actual A6 quotient constructs an
inverting involution z in N(E) ∩ N(⟨w⟩) outside N(F). The intermediate-subgroup
classification then gives X ∩ Xᶻ = B, using the absence of elements of order
ten to exclude the A5 quotient over E ∩ F. The literal subgroup Y = B⟨z⟩
has order 96 and the complete element-order census: one identity,
27 involutions, 32 elements of order three and 36 elements of order four.

The final application supplies all reflection premises of
`localConfiguration_of_reflection`. Only the independent X census remains
explicit in that application. Properness and index of the generated subgroup
belong to the later character argument in Lemma 17.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Janko's actual reflection, exact conjugate intersection and complete Y census,
for any supplied common order-three actor. -/
public theorem exists_reflection_geometry (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (w : FusedNineIntersectionActor D k) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ normalizer (CaseII.E D k : Set G) ∧
      z ∈ normalizer (zpowers w.actor : Set G) ∧
      z ∉ normalizer (CaseII.F D k : Set G) ∧
      X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom = B D k w ∧
      Nat.card (Y D k w z) = 96 ∧
      ∀ n : ℕ, Nat.card {y : Y D k w z // orderOf y = n} =
        localOrderCount 27 32 36 0 n := by
  obtain ⟨z, hz2, hzE, hzQ, hzF, hinv⟩ := exists_reflection D k L w hcard hN3 horders
  exact ⟨z, hz2, hzE, hzQ, hzF,
    conjugate_intersection_eq_B D k L horders w z hz2 hzE hzQ hzF,
    Y_card_of_reflection D k w z hz2 hzE hzQ hzF,
    Y_count_of_reflection D k w L z hz2 hzE hzQ hzF hinv⟩

/-- Apply the constructed reflection to the literal local-configuration consumer.
The independent census of X is the only remaining local-subgroup premise. -/
public theorem localConfiguration_of_X_census (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (hXcount : ∀ n : ℕ, Nat.card {x : X D k // orderOf x = n} =
      localOrderCount 75 320 180 384 n) : Nonempty (LocalConfiguration G) := by
  obtain ⟨w⟩ := exists_intersectionActor D k L
  obtain ⟨z, _, _, _, hzF, hinter, hYcard, hYcount⟩ :=
    exists_reflection_geometry D k L hcard hN3 horders w
  exact localConfiguration_of_reflection D k L w z hzF hinter hXcount hYcard hYcount

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
