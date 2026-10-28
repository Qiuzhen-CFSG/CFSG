module
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed

/-!
# Diagonal fixers of nonzero Hermitian Sylow-fixed vectors

The upper root group fixes exactly the upper singular line. Therefore a
diagonal matrix fixing any nonzero vector in that space fixes its specified
unit vector and has norm-one parameter. This is the coordinate calculation
in Aschbacher--Smith 10.1.2(5), printed p.742.
-/
public noncomputable section
namespace Representation.OrthogonalFourMinus.CartanFixed
open FiniteModel RankOne
variable (n : ℕ) [NeZero n]

theorem fixes_rootVector_of_nonzero_upper_fixed (a : (Field n)ˣ) (v : Space n)
    (hv : v ≠ 0)
    (hU : ∀ g : Matrix.SpecialLinearGroup.upperUnipotent (Field n), action n g v = v)
    (ha : action n (diagonal n a) v = v) :
    action n (diagonal n a) (rootVector n 1) = rootVector n 1 := by
  let w : Representation.invariants ((action n).comp
      (Matrix.SpecialLinearGroup.upperUnipotent (Field n)).subtype) := ⟨v,hU⟩
  let k := upperFixedEquivK n w
  have he : v = rootVector n k := congrArg Subtype.val
    ((upperFixedEquivK n).symm_apply_apply w).symm
  have hk : k ≠ 0 := by
    intro hk
    apply hv
    rw [he,hk]
    exact (coordinates n).symm.map_zero
  rw [he,diagonal_rootVector] at ha
  have hnorm : FiniteModel.norm n a = 1 := by
    have hh := congrArg (fun x : Space n => x.val 0 0) ha
    have hmul : FiniteModel.norm n a * k = k := Subtype.ext hh
    exact (mul_eq_right₀ hk).mp hmul
  rw [diagonal_rootVector,hnorm,one_mul]
end Representation.OrthogonalFourMinus.CartanFixed
