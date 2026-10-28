module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
import all CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
/-!
# The literal projection of the moved-star transport

The equation identifies the actual transported component map with the original
star-image surjection. The implementation import is an intentional internal
split: clients use this equation and do not unfold the unexposed projection.

Source: Aschbacher–Smith C.2.7, pp.145–147.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G D : Type*} [Group G] [Group D] {K R : Subgroup G}
    {J : Subgroup (StarQuotient K R)}
theorem starMovedProjection_apply (hCJ : starImage K R K ≤ J)
    (e : (starImage K R K).subgroupOf J ≃* D) (k : K) :
    starMovedProjection hCJ e k =
      e ((subgroupOfEquivOfLe hCJ).symm (toStarImage K R k)) := by rfl
end CFSG.Quasithin.ChapterC.C27Source
