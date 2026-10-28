module

public import Theory.GroupTheory.FixedPointFreeCyclicJoin
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionExistence
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionFixedPoints

/-!
# The actual subgroups in Janko's fixed-space construction

`X` is the ambient image of the derived subgroup of `N(F)`. For an actual
common order-three actor `w`, `B` is `E⟨w⟩`, and `Y` adjoins an element `z`
to `B`. No properness or index assertion is included in these definitions.

The two normalizer complements supply such an actor, using the existing
intersection construction. Its fixed-point-free action on E places E in X:
the commutator map on E is surjective, so every element of E is a commutator
of elements of N(F). Normality here is relative to the indicated normalizer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The actual ambient derived subgroup `(N(F))'`. -/
@[expose] public def X : Subgroup G :=
  ⁅normalizer (CaseII.F D k : Set G), normalizer (CaseII.F D k : Set G)⁆

/-- The source subgroup `EQ*`, for the actual intersection actor. -/
@[expose] public def B (w : FusedNineIntersectionActor D k) : Subgroup G :=
  CaseII.E D k ⊔ zpowers w.actor

/-- The source subgroup `EQ*Z*`, when `z` is its selected involution. -/
@[expose] public def Y (w : FusedNineIntersectionActor D k) (z : G) : Subgroup G :=
  B D k w ⊔ zpowers z

/-- The definition uses the derived subgroup of the normalizer, mapped into G. -/
public theorem X_eq_map_commutator : X D k =
    (_root_.commutator (normalizer (CaseII.F D k : Set G))).map
      (normalizer (CaseII.F D k : Set G)).subtype :=
  (map_subtype_commutator _).symm

/-- The derived subgroup is contained in the original F-normalizer. -/
public theorem X_le_normalizer_F : X D k ≤ normalizer (CaseII.F D k : Set G) :=
  commutator_le_self _

/-- All of `EQ*` normalizes E. -/
public theorem B_le_normalizer_E (w : FusedNineIntersectionActor D k) :
    B D k w ≤ normalizer (CaseII.E D k : Set G) :=
  sup_le le_normalizer (zpowers_le.mpr w.normalizes_E)

/-- All of `EQ*` also normalizes F. -/
public theorem B_le_normalizer_F [Finite G] (w : FusedNineIntersectionActor D k) :
    B D k w ≤ normalizer (CaseII.F D k : Set G) :=
  sup_le ((CaseII.E_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_F D k))
    (zpowers_le.mpr w.normalizes_F)

/-- The original local analysis supplies the common fixed-point-free actor. -/
public theorem exists_intersectionActor [Finite G] (L : LocalAnalysisData D k) :
    Nonempty (FusedNineIntersectionActor D k) := by
  let h2 : InvolutionNormalizerData D k :=
    ⟨L.normalizer_E, L.normalizer_F, L.involution_fusion⟩
  obtain ⟨q, hqE, hqF, hq3⟩ := exists_three_in_normalizer_intersection D k h2
  exact ⟨{ actor := q
           normalizes_E := hqE
           normalizes_F := hqF
           actor_order := hq3
           fixed_point_free := intersection_three_fixed_point_free D k h2 q hqE hqF hq3 }⟩

/-- The fixed-point-free actor puts E inside the literal derived F-normalizer. -/
public theorem E_le_X_of_actor [Finite G] (w : FusedNineIntersectionActor D k) :
    CaseII.E D k ≤ X D k :=
  le_commutator_of_fixedPointFree (CaseII.E D k) (normalizer (CaseII.F D k : Set G))
    ((CaseII.E_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_F D k))
    w.actor w.normalizes_E w.normalizes_F w.fixed_point_free

/-- The E-containment in Janko's first paragraph follows from the original local data. -/
public theorem E_le_X [Finite G] (L : LocalAnalysisData D k) : CaseII.E D k ≤ X D k := by
  obtain ⟨w⟩ := exists_intersectionActor D k L
  exact E_le_X_of_actor D k w

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
