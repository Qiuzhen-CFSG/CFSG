module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointResidual

/-!
# The point residual moves the middle chief factor

The elementary matrix adding the fourth coordinate to the third belongs
to the two-space parabolic residual. Its action on the exterior basis
sends a vector of V₇ to a vector differing outside V₁. Thus the original
residual acts nontrivially on V₇/V₁.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820.
-/

public section
open Subgroup

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem pointResidual_moves_middle :
    ∃ g ∈ parabolicResidual 2, ∃ v ∈ V₇,
      exteriorAction 2 g v - v ∉ V₁ := by
  have hp : elementary 2 3 ∈ parabolic 2 := by
    rw [parabolic_eq_closure_transvections]
    exact subset_closure ⟨2, 3, by decide, 1, by decide, by simp [elementary]⟩
  have hg : elementary 2 3 ∈ parabolicResidual 2 := by
    rw [parabolicResidual_two]
    refine ⟨⟨_, hp⟩, ?_, rfl⟩
    change parabolicTwoSmallBlock ⟨_, hp⟩ = 1
    apply Subtype.ext
    ext a b
    rw [parabolicTwoSmallBlock_entry]
    have hb : (3 : ℕ) ≠ b.val := by omega
    simp [elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single, Matrix.one_apply, Fin.ext_iff, hb]
  refine ⟨elementary 2 3, hg, basis 2, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨2, by decide, rfl⟩
  · have he : exteriorAction 2 (elementary 2 3) (basis 2) - basis 2 = basis 1 := by
      apply coordinates.injective
      rw [map_sub, coordinates_action, coordinates_basis, coordinates_basis]
      decide +kernel
    rw [he, V₁, mem_coordinateSpan]
    intro hh
    have hn := hh 1 (by decide)
    rw [coordinates_basis] at hn
    norm_num at hn
end Representation.SL5ExteriorSquare
