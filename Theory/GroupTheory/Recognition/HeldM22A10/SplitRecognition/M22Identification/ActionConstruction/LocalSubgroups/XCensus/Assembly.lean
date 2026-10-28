module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus

/-!
# Discharging the X census in the local-configuration consumer

Apply the complete census to the original reflection-assembly theorem. The
remaining premises describe the reflection, its literal conjugate intersection
and the Y census. Their construction stays with the local-subgroups assembly;
this theorem has no residual X-census or action premise.

Source: Janko (1968), Section 8, Lemma 17, pp.16--17.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The existing local-configuration assembly with its X census discharged. -/
public theorem localConfiguration_of_reflection_with_X_census (L : LocalAnalysisData D k)
    (w : FusedNineIntersectionActor D k) (z : G)
    (hz : z ∉ normalizer (CaseII.F D k : Set G))
    (hinter : X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom = B D k w)
    (hYcard : Nat.card (Y D k w z) = 96)
    (hYcount : ∀ n : ℕ, Nat.card {y : Y D k w z // orderOf y = n} =
      localOrderCount 27 32 36 0 n) : Nonempty (LocalConfiguration G) :=
  localConfiguration_of_reflection D k L w z hz hinter (X_count D k L) hYcard hYcount

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
