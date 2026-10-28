module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.Generation
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.Marking
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.NormalizerTransport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.EvenOvergroups
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore

/-!
# Geometry for the relative G₂ parabolic overgroups

The two parabolics generate the actual derived model, including G₂(2)′.
Pullback then gives generation of L and of ⟨L,S⟩ by the two overgroups.
The model isomorphism or central quotient can be chosen to mark the actual
Sylow intersection S ∩ L. Its characteristic kernel permits descent of the
relative normalizer action. Intrinsic Sylow-stabilizer invariance constructs
the remaining parabolic-coordinate fields.

The concrete short- and long-parabolic core calculations, followed by the
component-orbit transfer, prove that both overgroups belong to HeOver.
All geometric premises are discharged, including for G₂(2)′ and every
permitted central two-cover of G₂(4). The subsequent block argument giving
the source G₂ exclusion is separate.

Source: Aschbacher–Smith 1.1.5(3)(a,b), printed pp.501–502, and the proof of
2.3.9(7), printed p.526. All joins use the full supplied S, which is permitted
to permute components.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup

variable {G : Type*} [Group G]

/-- Intrinsic invariance supplies the two relative normalizer fields of a
marked model, retaining its actual map and entire permitted kernel. -/
def SylowModel.toParabolicCoordinates {L S : Subgroup G} (d : SylowModel L S) :
    ParabolicCoordinates L S :=
  d.coordinatesOfStabilizerInvariant
    (fun b hb => Atlas.G2.SylowParabolicInvariance.restricted_parabolics_invariant b hb)

/-- Construct the genuine parabolic coordinates from either source G₂ model
case and the supplied component Sylow intersection. -/
theorem exists_parabolicCoordinates {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (hmodel : IsModelCase L) :
    Nonempty (ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) := by
  obtain ⟨d⟩ := exists_sylowModel h hmodel
  exact ⟨d.toParabolicCoordinates⟩

/-- The two relative G₂ parabolic overgroups required in the proof of
2.3.9(7): they generate an overgroup of L and both lie in HeOver of the
full supplied Sylow subgroup. No additional model or geometry premise remains. -/
theorem exists_parabolicCoordinates_HeOver
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (hmodel : IsModelCase L)
    (hinner : ∃ t : L, IsConjugationProjection L z t) :
    ∃ d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype),
      L ≤ d.firstOvergroup ⊔ d.secondOvergroup ∧
      d.firstOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) ∧
      d.secondOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  obtain ⟨d⟩ := exists_parabolicCoordinates h hmodel
  exact ⟨d, d.le_overgroups_sup, d.overgroups_mem_HeOver h hinner
    (fun _ => Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore)⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
