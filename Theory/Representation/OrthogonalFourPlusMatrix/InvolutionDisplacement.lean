module

public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Involutions in the binary determinant action

For a nonidentity involution in the literal `SL₂(4) × SL₂(4)` action,
every fixed matrix is a displacement. The displacement map squares to zero
in characteristic two. Its range has dimension at least four by the
determinant-action rank bound, and rank-nullity in dimension eight then
identifies its range and kernel.

This supplies the commutator calculation for central involutions in the
tensor point argument of Aschbacher–Smith, 9.4.1, printed pp.735–736. The
underlying displacement bound is also used in 13.8.16(1), printed pp.952–953.
-/

@[expose] public section
namespace ClassicalOrthogonal.FourPlusMatrix.InvolutionDisplacement
open Module Binary

/-- The displacement image of an involution is contained in its fixed space. -/
theorem displacement_range_le_ker (g : G) (hg : g ^ 2 = 1) :
    LinearMap.range (action g - LinearMap.id) ≤
      LinearMap.ker (action g - LinearMap.id) := by
  rintro w ⟨a, rfl⟩
  change action g (action g a - a) - (action g a - a) = 0
  have haa : action g (action g a) = a := by
    change (action g * action g) a = a
    rw [← map_mul, ← pow_two, hg, map_one]
    rfl
  apply sub_eq_zero.mpr
  rw [map_sub, haa]
  apply sub_eq_sub_iff_add_eq_add.mpr
  apply Matrix.ext
  intro i j
  exact (CharTwo.add_self_eq_zero (a i j)).trans
    (CharTwo.add_self_eq_zero (action g a i j)).symm

/-- A nonidentity involution has equal displacement image and fixed space. -/
theorem displacement_range_eq_ker (g : G) (hg : g ≠ 1) (hg₂ : g ^ 2 = 1) :
    LinearMap.range (action g - LinearMap.id) =
      LinearMap.ker (action g - LinearMap.id) := by
  apply Submodule.eq_of_le_of_finrank_le (displacement_range_le_ker g hg₂)
  have hr := Displacement.displacement_rank_four g hg
  have hd := LinearMap.finrank_range_add_finrank_ker (action g - LinearMap.id)
  rw [finrank_binary] at hd
  omega

/-- Every vector fixed by a nonidentity involution is a displacement by it. -/
theorem exists_displacement_of_fixed (g : G) (hg : g ≠ 1) (hg₂ : g ^ 2 = 1)
    (w : V) (hw : action g w = w) :
    ∃ a : V, action g a - a = w := by
  have hk : w ∈ LinearMap.ker (action g - LinearMap.id) := by
    change action g w - w = 0
    exact sub_eq_zero.mpr hw
  rw [← displacement_range_eq_ker g hg hg₂] at hk
  exact hk

end ClassicalOrthogonal.FourPlusMatrix.InvolutionDisplacement
