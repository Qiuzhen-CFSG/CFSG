module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.Octad
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.Sextet
public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet

/-!
# Block obstructions in the lifted M₂₄ geometry

The octad branch is proved from the actual A₈ quotient. The sextet branch
uses the proved native subgroup calculation `subnormal_sextet_orders`.
Central-orbit coordinates retain O₂(L), relative subnormality and possible
permutation of components by S. The full short-group definition and the
actual χ₀ quotient models, including the cubic module case, are used.

`blockObstruction_of_geometry` supplies exactly the `hobs` argument of
`cover_of_geometry_pair`, with the native sextet premise discharged.
`cover_of_geometry_pair_of_localSetup` applies it to both locals of the
supplied geometric pair. Constructing that pair and assembling the full
M₂₄ exclusion remain with the caller.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, especially the sporadic
paragraph; C.1.7 and C.1.12, printed pp.123–124.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
open Subgroup Sporadic.Mathieu M24LocalGeometry
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Exact geometric-local obstruction, conditional only on the remaining
intrinsic sextet subgroup orders. -/
theorem blockObstruction_of_geometry_of_sextet_orders
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m24)
    (horders : ∀ X : Sextet, SubnormalSextetOrders (sextetStabilizer X))
    (P : Subgroup M24) (hgeometry : IsGeometryLocal P)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) P = lift d P)
    (_he : localOvergroup d ((S : Subgroup H).map H.subtype) P ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (localOvergroup d ((S : Subgroup H).map H.subtype) P) := by
  rcases hgeometry with ⟨O, rfl⟩ | ⟨X, rfl⟩
  · exact octad_blockObstruction h d O hinter
  · exact sextet_blockObstruction_of_orders h d X hinter (horders X)

/-- Apply the block calculation to the literal two locals in a geometric
pair. The caller still constructs the pair and proves the native sextet orders. -/
theorem cover_of_geometry_pair_of_sextet_orders
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m24)
    (pair : GeometryPair d ((S : Subgroup H).map H.subtype))
    (horders : ∀ X : Sextet, SubnormalSextetOrders (sextetStabilizer X)) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  cover_of_geometry_pair d _ pair
    (blockObstruction_of_geometry_of_sextet_orders h d horders)

/-- Every allowed moved block of an actual geometric local lies in M.
The intrinsic sextet orders are proved on the native M₂₄ carrier; no
subgroup-classification or block-obstruction premise remains. -/
theorem blockObstruction_of_geometry
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m24)
    (P : Subgroup M24) (hgeometry : IsGeometryLocal P)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) P = lift d P)
    (he : localOvergroup d ((S : Subgroup H).map H.subtype) P ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (localOvergroup d ((S : Subgroup H).map H.subtype) P) :=
  blockObstruction_of_geometry_of_sextet_orders h d subnormal_sextet_orders
    P hgeometry hinter he

/-- Apply the proved obstruction to the literal two locals of a geometric
pair, retaining the original component quotient and supplied Sylow subgroup. -/
theorem cover_of_geometry_pair_of_localSetup
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m24)
    (pair : GeometryPair d ((S : Subgroup H).map H.subtype)) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  cover_of_geometry_pair d _ pair (blockObstruction_of_geometry h d)

end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
end
