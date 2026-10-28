module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.ExteriorAction.RealSpace

/-!
# The SU₄(3) permutation action on the fixed 252 points

The invariant real exterior space and preservation of its quadratic form place
the image of each published nonisotropic vector in a unique sign class.
Functoriality of the compound matrix gives composition, and the inverse SU
matrix supplies the inverse permutation. No orbit or generation calculation
is needed. This is the action before quotienting out the scalar matrices.

Source: GLS3 §2.7, as used in the concrete cover comparison for
Aschbacher–Smith I.1.4(5), p.408. The exterior identities are supplied by the
attributed ATLAS port; see LICENSES/ATLAS.txt.

-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
open Matrix Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary

def pointImage (g : SU4) (i : Index) : Index :=
  indexOf (realCoordinates (exteriorSU g (point i)))

theorem pointImage_spec (g : SU4) (i : Index) :
    exteriorSU g (point i) = point (pointImage g i) ∨
      exteriorSU g (point i) = -point (pointImage g i) := by
  have hn : norm (realCoordinates (exteriorSU g (point i))) ≠ 0 := by
    rw [point, exterior_norm]
    exact coordinates_norm_ne_zero i
  have hb := exterior_bivector g (coordinates i)
  change bivector (realCoordinates (exteriorSU g (point i))) = exteriorSU g (point i) at hb
  rcases coordinates_complete _ hn with h | h
  · exact Or.inl (hb.symm.trans (congrArg bivector h))
  · exact Or.inr (hb.symm.trans ((congrArg bivector h).trans (bivector_neg _)))

theorem pointImage_one (i : Index) : pointImage 1 i = i := by
  apply point_eq_of_sign_choices (pointImage_spec 1 i)
  exact Or.inl (by rw [map_one]; rfl)

theorem pointImage_mul (g h : SU4) (i : Index) :
    pointImage (g * h) i = pointImage g (pointImage h i) := by
  apply point_eq_of_sign_choices (pointImage_spec (g * h) i)
  rw [map_mul]
  change exteriorSU g (exteriorSU h (point i)) = _ ∨
    exteriorSU g (exteriorSU h (point i)) = _
  rcases pointImage_spec h i with hh | hh
  · rw [hh]
    exact pointImage_spec g (pointImage h i)
  · rw [hh, map_neg]
    rcases pointImage_spec g (pointImage h i) with hg | hg
    · exact Or.inr (congrArg Neg.neg hg)
    · exact Or.inl (by rw [hg, neg_neg])

def specialPointAction : SU4 →* Equiv.Perm Index where
  toFun g :=
    { toFun := pointImage g
      invFun := pointImage g⁻¹
      left_inv := by intro i; rw [← pointImage_mul, inv_mul_cancel, pointImage_one]
      right_inv := by intro i; rw [← pointImage_mul, mul_inv_cancel, pointImage_one] }
  map_one' := by apply Equiv.ext; intro i; exact pointImage_one i
  map_mul' g h := by apply Equiv.ext; intro i; exact pointImage_mul g h i

@[simp] theorem specialPointAction_apply (g : SU4) (i : Index) :
    specialPointAction g i = pointImage g i := rfl

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
