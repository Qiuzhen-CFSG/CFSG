module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Outer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Ratios

/-!
# Discharging the outer hypotheses of the tensor ratio assembly

The actual outer-action exclusions supply the exact `houter` premises of
all three ratio consumers. Only the earlier inner dimension and inner
quadratic rank inputs remain explicit; the parent tensor task owns their
source discharge and the existence of a marked Sylow.

Source: Aschbacher–Smith, K.3.2.4, printed pp.455–456/PDF pp.466–467.
-/

public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

include hM in
/-- The cubic-ratio assembly now needs only the genuine earlier inner dimensions. -/
theorem cubicRatio_eq_of_inner_source_dimensions
    (hroot : InnerRootDimensions n M) (hlarge : InnerLargeRankCodimension n M) :
    cubicRatio (overgroupAction n M) = 5 / 4 :=
  cubicRatio_eq_of_inner_dimensions n M hM hroot hlarge (small_actor_le_inner n M hM)

/-- The marked-Sylow classification with its outer-exclusion premise discharged. -/
theorem small_actor_iff_eq_plane_of_inner_source_dimensions
    (hroot : InnerRootDimensions n M) (hlarge : InnerLargeRankCodimension n M)
    (T : Sylow 2 M) (hT : IsMarkedSylow n M hM T) (A : Subgroup M) :
    (IsElementaryTwo A ∧ A ≤ T ∧ actionRatio (overgroupAction n M) A ≤ 5 / 4) ↔
      A = planeActor n M hM :=
  small_actor_iff_eq_plane n M hM hroot hlarge (small_actor_le_inner n M hM) T hT A

include hM in
/-- Quadratic exclusion is reduced solely to the inner root and rank calculations. -/
theorem quadraticRatio_gt_two_of_inner_source_rank
    (hroot : InnerRootDimensions n M)
    (hquad : ∀ A : Subgroup M, IsElementaryTwo A → A ≤ innerActor n M →
      IsQuadratic (overgroupAction n M) A → rank A ≤ n) :
    2 < quadraticRatio (overgroupAction n M) :=
  quadraticRatio_gt_two_of_inner_rank n M hroot (quadratic_actor_le_inner n M hM) hquad

end CFSG.Quasithin.ChapterK.Linear.Tensor
