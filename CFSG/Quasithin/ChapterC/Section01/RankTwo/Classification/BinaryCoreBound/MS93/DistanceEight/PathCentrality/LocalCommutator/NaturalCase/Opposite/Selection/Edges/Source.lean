module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Source

/-!+# The selected opposite parabolic for the initial edge calculation

The source chooses a parabolic stabilizing the moving class in W/B_c.
In the opposite orientation this parabolic has no fixed points on U_c,
and it normalizes the original cyclic displacement in the amalgam. The
record below retains that actual parabolic through the frame's projection.
It records a proof output; its existence is not asserted here.

The independent small-displacement calculation must put this normalized
subgroup in U_c and prove that it has order four. Neither conclusion is
a field of this record. The algebra in the parent Edges module then proves
the two edge identities and the kernel centralizer product.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), printed
pp.890–891, the choice of x and normalization by a conjugate of F₂.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The source's actual opposite parabolic and moving element, before the
displacement has been identified with either endpoint's edge subgroup. -/
structure ParabolicSeed (geometry : Geometry R) {a c : Vertex R} (f : FrameAt a c)
    extends MovingSeed a c where
  flag : SL
  weakBN : BinaryWeakBN flag
  side : Bool
  natural_fixed_eq_bot : (U R c).subgroupOf (stabilizer R c) ⊓
    centralizer (parabolic f.sectionData.projection flag side : Set (stabilizer R c)) = ⊥
  class_fixed : ⁅zpowers element,
    (parabolic f.sectionData.projection flag side).map (stabilizer R c).subtype⁆ ≤
      B R c (geometry.Z_normal c)
  displacement_normalized :
    (parabolic f.sectionData.projection flag side).map (stabilizer R c).subtype ≤
      normalizer (⁅zpowers element, Q R c⁆ : Subgroup (FreeAmalgam R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
