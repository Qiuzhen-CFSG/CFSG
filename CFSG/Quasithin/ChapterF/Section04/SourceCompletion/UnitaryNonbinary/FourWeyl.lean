module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Models
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.NativeWeyl
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan

/-!
# Native Weyl-defect control for full PSU₄ extensions

The literal native point and plane reflections map into any faithful
completion of the marked full extension. The native Borel centralizer
calculation proves that a power of their product in the native overlap
is trivial. A power in the full overlap has square one, leaving a possible
outer involution. This includes q = 4 and even extension degrees.

Source: the direct Cartan route in Aschbacher–Smith F.4.10,16–17,
printed pp.279,282–283 of `refs/quasithin.pdf`. Apartment closure and
elimination of the outer defect remain necessary for recognition.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)

def point : pointParabolic m hm :=
  ⟨projection m hm (middleSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)),
    ⟨_,middleSwap_mem_point _ _ _,rfl⟩⟩

def plane : planeParabolic m hm :=
  ⟨projection m hm (pairSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)),
    ⟨_,pairSwap_mem_plane _ _ _,rfl⟩⟩

theorem point_sq : point m hm ^ 2 = 1 := by
  let s : MatrixGroup m hm := middleSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  have hs : s^2=1 := SmallCompletion.FourCartan.middleSwap_sq _ _ _
  apply Subtype.ext
  exact (map_pow (projection m hm) s 2).symm.trans
    ((congrArg (projection m hm) hs).trans (map_one _))

theorem plane_sq : plane m hm ^ 2 = 1 := by
  let s : MatrixGroup m hm := pairSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  have hs : s^2=1 := SmallCompletion.FourCartan.pairSwap_sq _ _ _
  apply Subtype.ext
  exact (map_pow (projection m hm) s 2).symm.trans
    ((congrArg (projection m hm) hs).trans (map_one _))

/-- The native overlap has trivial centralizer of the marked quarter-turn.
The projective projection is the actual injective SU₄ projection. -/
theorem overlap_rotation_centralizer
    (b : (pointParabolic m hm ⊓ planeParabolic m hm : Subgroup (ProjectiveGroup m hm)))
    (hr : Commute b.val ((plane m hm).val*(point m hm).val)) : b.val=1 := by
  have hb : b.val ∈ overlap m hm := (exact_overlap m hm) ▸ b.property
  change b.val ∈ (borelSU (MatrixField m) (standardForm m hm)).map (projection m hm) at hb
  apply SmallCompletion.FourCartan.borel_project_commute_rotation
    (MatrixField m) (fieldConj m) (fieldConj_involutive m hm) b.val hb
  let s : MatrixGroup m hm := middleSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  let t : MatrixGroup m hm := pairSwap (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  have hh : Commute b.val (projection m hm (t*s)) := by
    rw [map_mul]
    exact hr
  exact hh

variable (E : FourExtension m hm) {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

def rotation : M := E.nativeRotation c (point m hm) (plane m hm)

/-- A power of the actual completion rotation is in the native overlap
exactly when it is trivial. This is stronger than the diagonal-torus test. -/
theorem power_eq_one_iff_nativeOverlap (k : ℕ) :
    rotation m hm E c ^ k = 1 ↔ rotation m hm E c ^ k ∈ (E.innerMiddle c).range := by
  constructor
  · intro h
    rw [h]
    exact one_mem _
  · exact E.nativeRotation_power_eq_one_of_native_overlap c (four_conj_injective m hm)
      (point m hm) (plane m hm) (point_sq m hm) (plane_sq m hm)
      (overlap_rotation_centralizer m hm) k

/-- The full overlap can still carry an outer involution. Its square is
native, so the marked rotation power has square one. -/
theorem power_sq_eq_one_of_middle (k : ℕ)
    (h : rotation m hm E c ^ k ∈ c.middle.range) :
    (rotation m hm E c ^ k)^2 = 1 :=
  E.nativeRotation_power_sq_eq_one_of_middle c (four_conj_injective m hm)
    (point m hm) (plane m hm) (point_sq m hm) (plane_sq m hm)
    (overlap_rotation_centralizer m hm) k h
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
