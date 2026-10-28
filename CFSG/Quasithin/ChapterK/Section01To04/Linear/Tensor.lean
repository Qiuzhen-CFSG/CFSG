module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Outer.Applications
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Quadratic

/-!
# The actual Hermitian tensor branch of K.3.2.4

On the descended binary module of dimension 9n, the literal plane radical
has rank 4n, fixed dimension 4n and cubic action. It attains ratio 5/4.
The point radical has the same rank but fixed dimension n and ratio two.
All maps use the actual faithful image; Chapter H's comparisons preserve
SL₃(2^(2n)) for even n and PSL₃(2^(2n)) for odd n.

The assembly below discharges the outer-actor exclusions and the inner
quadratic rank bound using the actual actions, and constructs a marked
Sylow. It proves the strict quadratic bound, the cubic ratio and the unique
small elementary actor in that Sylow. The quadratic calculation uses the
second displacement in both radicals, avoiding the printed conflation of
the root's moved space (dimension 4n) with its fixed space (dimension 5n).

Only `InnerRootDimensions` and `InnerLargeRankCodimension`, the explicitly
stated earlier H.4.4 inputs, remain hypotheses. Their discharge belongs to
the parent linear-family assembly, using the parabolic source results;
these conditional theorems do not certify that upstream result. Module
recognition also remains with that parent. All earlier conditional APIs,
the point-radical alternative and the SL/PSL comparisons are re-exported.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467.
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
/-- The quadratic conclusion of K.3.2.4, with only the earlier root-dimension
input left explicit. Both action exclusions are proved on the literal image. -/
theorem quadraticRatio_gt_two_of_inner_source_dimensions
    (hroot : InnerRootDimensions n M) :
    2 < quadraticRatio (overgroupAction n M) :=
  quadraticRatio_gt_two_of_root_and_outer n M hM hroot
    (quadratic_actor_le_inner n M hM)

include hM in
/-- Both ratios for the actual descended tensor, conditional solely on the
specified earlier H.4.4 dimensions. The parent must discharge those inputs. -/
theorem ratios_of_inner_source_dimensions
    (hroot : InnerRootDimensions n M) (hlarge : InnerLargeRankCodimension n M) :
    2 < quadraticRatio (overgroupAction n M) ∧
      cubicRatio (overgroupAction n M) = 5 / 4 :=
  ⟨quadraticRatio_gt_two_of_inner_source_dimensions n M hM hroot,
    cubicRatio_eq_of_inner_source_dimensions n M hM hroot hlarge⟩

/-- The attaining plane radical and the full small-actor classification in a
constructed marked Sylow. The point radical remains an alternative for general
elementary inner actors, but its ratio two excludes it from this singleton. -/
theorem plane_minimizer_of_inner_source_dimensions
    (hroot : InnerRootDimensions n M) (hlarge : InnerLargeRankCodimension n M) :
    ∃ T : Sylow 2 M, IsMarkedSylow n M hM T ∧
      IsElementaryTwo (planeActor n M hM) ∧
      IsCubic (overgroupAction n M) (planeActor n M hM) ∧
      rank (planeActor n M hM) = 4 * n ∧
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n M) (planeActor n M hM)) = 4 * n ∧
      actionRatio (overgroupAction n M) (planeActor n M hM) = 5 / 4 ∧
      ∀ A : Subgroup M,
        (IsElementaryTwo A ∧ A ≤ T ∧ actionRatio (overgroupAction n M) A ≤ 5 / 4) ↔
          A = planeActor n M hM := by
  obtain ⟨T, hT⟩ := exists_markedSylow n M hM
  exact ⟨T, hT, planeActor_elementary n M hM, planeActor_cubic n M hM,
    rank_planeActor n M hM, finrank_plane_fixed n M hM, planeActor_ratio n M hM,
    small_actor_iff_eq_plane_of_inner_source_dimensions n M hM hroot hlarge T hT⟩

end CFSG.Quasithin.ChapterK.Linear.Tensor
