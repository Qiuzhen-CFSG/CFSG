module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveCensus
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.NativeWeyl
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveCartan

/-!
# Native Weyl-defect control for full PSU₅(4) extensions

Transport the actual hyperbolic reflections through the projective native
parabolics and the faithful full-extension completion maps. The projective
rotation centralizer kills every rotation power in the native overlap.
A power in the full overlap has square one. The order-five scalar kernel
and all outer factors are retained throughout these calculations.

Source: Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283 of
`refs/quasithin.pdf`. These are algebraic defect bounds; apartment closure
and elimination of a possible outer involution are still required.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
open SmallCompletion.FivePaths
variable (U : GreenBook.UnitaryFive.Model 4)
variable (t : U.F) (ht : t + U.form.conj t = 1)

def point : U.leftParabolic :=
  ⟨project U.form (middleSwap U.form t ht U.matrix),
    ⟨_,middleSwap_mem_line U.form t ht U.matrix,rfl⟩⟩

def plane : U.rightParabolic :=
  ⟨project U.form (pairSwap U.form t ht U.matrix),
    ⟨_,pairSwap_mem_plane U.form t ht U.matrix,rfl⟩⟩

theorem point_sq : point U t ht ^ 2 = 1 := by
  apply Subtype.ext
  change (project U.form _ )^2 = 1
  rw [←map_pow,middleSwap_sq,map_one]

theorem plane_sq : plane U t ht ^ 2 = 1 := by
  apply Subtype.ext
  change (project U.form _ )^2 = 1
  rw [←map_pow,pairSwap_sq,map_one]

/-- The native projective overlap centralizer is trivial; the SU scalar
kernel of order five is retained in the proof. -/
theorem overlap_rotation_centralizer
    (b : (U.leftParabolic ⊓ U.rightParabolic : Subgroup U.Carrier))
    (hr : Commute b.val ((plane U t ht).val*(point U t ht).val)) : b.val=1 := by
  apply SmallCompletion.FiveCartan.projective_line_commute_rotation
    U.form t ht U.matrix U.conjugation U.card b.val b.property.1
  change Commute b.val (project U.form (pairSwap U.form t ht U.matrix) *
    project U.form (middleSwap U.form t ht U.matrix)) at hr
  simpa only [SmallCompletion.FivePaths.rotation,map_mul] using hr

variable (E : FiveExtension U) {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

def rotation : M := E.nativeRotation c (point U t ht) (plane U t ht)

/-- Native-overlap localization kills any power of the actual rotation.
No assertion about the full overlap is substituted for this premise. -/
theorem power_eq_one_iff_nativeOverlap (k : ℕ) :
    rotation U t ht E c ^ k = 1 ↔ rotation U t ht E c ^ k ∈ (E.innerMiddle c).range := by
  constructor
  · intro h
    rw [h]
    exact one_mem _
  · exact E.nativeRotation_power_eq_one_of_native_overlap c (five_conj_injective U)
      (point U t ht) (plane U t ht) (point_sq U t ht) (plane_sq U t ht)
      (overlap_rotation_centralizer U t ht) k

/-- A rotation power in the full overlap has square one. This leaves the
possible outer involution explicit, including extensions of even degree. -/
theorem power_sq_eq_one_of_middle (k : ℕ)
    (h : rotation U t ht E c ^ k ∈ c.middle.range) :
    (rotation U t ht E c ^ k)^2 = 1 :=
  E.nativeRotation_power_sq_eq_one_of_middle c (five_conj_injective U)
    (point U t ht) (plane U t ht) (point_sq U t ht) (plane_sq U t ht)
    (overlap_rotation_centralizer U t ht) k h
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
