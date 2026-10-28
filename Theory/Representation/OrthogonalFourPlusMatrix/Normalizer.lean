module

public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement
public import Theory.Representation.BinaryNormalizerRank
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# No binary transvections in the determinant-action normalizer

The concrete determinant action has displacement rank at least four on every
nonidentity element and has no common nonzero fixed vector. The rank argument
in `BinaryNormalizerRank` therefore excludes transvections from its full
binary linear normalizer. In particular the conclusion applies to any binary
linear action with a normal subgroup whose actual image is this matrix group.
No semilinearity or description of the full normalizer is assumed.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
The comparison with the Siegel-generated orthogonal carrier is separate.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Module

/-- The full binary normalizer of the determinant action contains no transvection. -/
theorem normalizer_no_transvection (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V))) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 1 := by
  apply Representation.BinaryNormalizerRank.normalizer_no_rank_one linearAction.range
    (t := t) (hn := ht)
  · rintro _ ⟨g, rfl⟩ hg
    have hg1 : g ≠ 1 := by
      intro he
      apply hg
      rw [he, map_one]
    exact (by decide : 3 ≤ 4).trans (Displacement.displacement_rank_four g hg1)
  · intro v hv
    exact Displacement.common_fixed_eq_zero v (fun g => hv (linearAction g) ⟨g, rfl⟩)

/-- A normal subgroup with the literal determinant-action image excludes
transvections in the extending action, even without faithfulness of that extension. -/
theorem extension_no_transvection {H : Type*} [Group H]
    (ρ : H →* (V ≃ₗ[ZMod 2] V)) (N : Subgroup H) [N.Normal]
    (himage : N.map ρ = linearAction.range) (h : H) :
    finrank (ZMod 2) (LinearMap.range ((ρ h).toLinearMap - LinearMap.id)) ≠ 1 := by
  apply normalizer_no_transvection
  rw [← himage]
  apply Subgroup.le_normalizer_map ρ
  apply Subgroup.mem_map_of_mem
  rw [Subgroup.normalizer_eq_top]
  trivial

end ClassicalOrthogonal.FourPlusMatrix.Binary
