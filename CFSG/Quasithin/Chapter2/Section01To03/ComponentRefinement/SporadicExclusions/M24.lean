module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction
public import Theory.Mathieu.M24.LocalGeometry.Seed

/-!
# M24 local block cover

Source: Aschbacher–Smith, 2.3.9(7), printed p.526.

Choose the native octad/sextet pair over the image of the component Sylow
subgroup, and pull it back through the specified map L → L/O₂(L) ≃ M24.
Adjoining the supplied Sylow subgroup gives two overgroups inside L ∨ S
with nontrivial self-centralizing two-cores. The geometric pair generates L,
and the subnormal-block calculations give the obstruction for both locals.
This constructs every field of `CentralizerBlockCover`, with no additional
geometry or block premise and without assuming that S normalizes L.

The parent sporadic exclusion assembly can apply
`LocalSetup.false_of_centralizerBlockCover` to this cover.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The M₂₄ calculation in 2.3.9(7): the actual component quotient supplies
a generating local block cover for the prescribed Sylow subgroup. -/
theorem nonempty_centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨pair⟩ := geometryPair_nonempty h d
  exact cover_of_geometry_pair_of_localSetup h d pair

end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
