module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.Exclusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalRecognition

/-!
# Unconditional recognition from the original G₂(3) configuration

The special-support character argument excludes the Sylow-nine branch.
The previously constructed large-three-core recognition therefore applies
to every original local configuration.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G]

/-- The original (G1)–(G2) configuration identifies the ambient group with
the actual ternary G₂ model, without a simplicity or recognition premise. -/
theorem nonempty_mulEquiv_of_original_configuration (c : G2ThreeConfiguration G) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) :=
  nonempty_mulEquiv_of_cube_dvd c (cube_dvd_of_original_configuration c)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
