module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.ModelRestriction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.CyclicFour

/-!
# Fixed-pair Clifford coordinates from the image-center calculation

The original two-core of the native disjoint-pair stabilizer preimage has
order 64, contains the embedded cyclic-four center, and has binary squares.
The independent recognition theorem therefore supplies its Clifford
coordinates once its image's full center is that cyclic-four layer.
The equivalence factors through `coreImageEquiv`, and its inverse retains
the actual ambient map into K through the incident hexad.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412, PDF pp.421 and
423 (combined manuscript, 1 March 2004). The hexad Recognition and the
image-center equality remain explicit earlier inputs. The parent owns
unconditional assembly and must discharge the center premise; the pair
core is never replaced by the hexad radical.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open EvenCliffordSix.SplitExtension.ElementaryRestrictions
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K] [Finite K] [IsCyclic (center K)]
variable (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
variable (rec : Recognition e m22Hexad234_mem)
variable (hcenter : center (coreImage e hZ rec) = centralIn (coreImage e hZ rec))

/-- The actual pair-core image is the Clifford model once its full center
has been identified with the embedded cyclic-four layer. -/
noncomputable def coreImageCliffordEquivOfCenter : coreImage e hZ rec ≃* EvenCliffordSix.Model :=
  equivOfCenter _ (coreImage_contains_central e hZ rec)
    (coreImage_card e hZ rec) (coreImage_square e hZ rec) hcenter

/-- The literal fixed-pair two-core, rather than the hexad radical, has
Clifford coordinates. Only the image-center calculation remains explicit. -/
noncomputable def fixedPairCoreEquivOfCenter :
    pCore 2 (preimage e m22DisjointPairStabilizer) ≃* EvenCliffordSix.Model :=
  (coreImageEquiv e hZ rec).trans (coreImageCliffordEquivOfCenter e hZ rec hcenter)

/-- The recognition map factors through the original embedded pair-core image. -/
@[simp] theorem fixedPairCoreEquivOfCenter_apply
    (x : pCore 2 (preimage e m22DisjointPairStabilizer)) :
    fixedPairCoreEquivOfCenter e hZ rec hcenter x =
      coreImageCliffordEquivOfCenter e hZ rec hcenter (coreImageEquiv e hZ rec x) := rfl

/-- Inverse Clifford coordinates retain the original ambient map into K
through the incident hexad, with the same literal core inclusion. -/
@[simp] theorem fixedPairCoreEquivOfCenter_symm_ambient (m : EvenCliffordSix.Model) :
    (((fixedPairCoreEquivOfCenter e hZ rec hcenter).symm m).val : K) =
      (rec.modelToHexad e m22Hexad234_mem
        ((coreImageCliffordEquivOfCenter e hZ rec hcenter).symm m).val : K) := by
  change (((coreImageEquiv e hZ rec).symm
    ((coreImageCliffordEquivOfCenter e hZ rec hcenter).symm m)).val : K) = _
  simpa only [MulEquiv.apply_symm_apply] using
    (coreImageEquiv_ambient e hZ rec ((coreImageEquiv e hZ rec).symm
      ((coreImageCliffordEquivOfCenter e hZ rec hcenter).symm m))).symm

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
