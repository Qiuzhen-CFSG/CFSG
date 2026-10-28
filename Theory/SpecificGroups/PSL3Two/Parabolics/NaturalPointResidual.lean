module

public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint

/-!
# The natural point residual in SL₃(2)

The point parabolic has order 24. Its two-residual has order 12 and the
same two-core. Two explicit displacement operators, a translation and a
cubic Levi element, generate the whole natural module. Conjugating the
standard point proves these facts at every nonzero natural vector.

The displacement calculation is used to lift the original seed into the
literal point residual in the order-32 branch of Aschbacher–Smith 14.4.4(5),
printed p.1007. It uses the natural action, not just an abstract quotient.
-/

@[expose] public section
open Subgroup
namespace BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem point_marking (v : Vector) (hv : v ≠ 0) :
    ∃ g : Group, naturalPoint v = pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three ![1,0,0] v (by decide) hv
  have he : naturalPoint ![1,0,0] = pointParabolicSL := by
    rw [← Matrix.PSL3Two.Fano.stabilizer_flagPoint_SL]
    ext a
    change a • (![1,0,0] : Vector) = ![1,0,0] ↔ a • flagPoint = flagPoint
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine ⟨g, ?_⟩
  change W g ![1,0,0] = v at hg
  rw [← hg, naturalPoint_action, he]

theorem naturalPoint_card (v : Vector) (hv : v ≠ 0) :
    Nat.card (naturalPoint v) = 24 := by
  obtain ⟨g, hg⟩ := point_marking v hv
  rw [hg, card_map_of_injective (MulAut.conj g).injective, card_pointParabolicSL]

theorem naturalPoint_residual_core (v : Vector) (hv : v ≠ 0) :
    (((pResidual 2 (naturalPoint v)).map (naturalPoint v).subtype).pCoreIn 2) =
      (naturalPoint v).pCoreIn 2 := by
  obtain ⟨g, hg⟩ := point_marking v hv
  rw [hg, ← map_embedded_pResidual]
  change ((residual pointParabolicSL).map (MulAut.conj g).toMonoidHom).pCoreIn 2 = _
  rw [← map_pCoreIn_of_injective 2 (residual pointParabolicSL) _ (MulAut.conj g).injective,
    ← map_pCoreIn_of_injective 2 pointParabolicSL _ (MulAut.conj g).injective,
    point_residual, point_core, MarkedProduct.pointParabolic_core]

theorem naturalPoint_residual_card (v : Vector) (hv : v ≠ 0) :
    Nat.card ((pResidual 2 (naturalPoint v)).map (naturalPoint v).subtype) = 12 := by
  obtain ⟨g, hg⟩ := point_marking v hv
  rw [hg, ← map_embedded_pResidual, card_map_of_injective (MulAut.conj g).injective]
  exact card_point_residual

private theorem standard_displacements : ∀ w : Vector, ∃ x y : Vector,
    w = (W (Bruhat.upper 1) x - x) + (W cubic y - y) := by decide +kernel

/-- The natural point residual generates the entire natural module by displacements. -/
theorem naturalPoint_residual_displacements (v : Vector) (hv : v ≠ 0) (w : Vector) :
    ∃ a ∈ (pResidual 2 (naturalPoint v)).map (naturalPoint v).subtype,
      ∃ b ∈ (pResidual 2 (naturalPoint v)).map (naturalPoint v).subtype,
        ∃ x y : Vector, w = (W a x - x) + (W b y - y) := by
  obtain ⟨g, hg⟩ := point_marking v hv
  have hr : (pResidual 2 (naturalPoint v)).map (naturalPoint v).subtype =
      pointA.map (MulAut.conj g).toMonoidHom := by
    rw [hg, ← map_embedded_pResidual]
    change (residual pointParabolicSL).map _ = _
    rw [point_residual]
  obtain ⟨x, y, he⟩ := standard_displacements (W g⁻¹ w)
  refine ⟨g * Bruhat.upper 1 * g⁻¹, hr ▸ mem_map_of_mem _ translations_mem.1,
    g * cubic * g⁻¹, hr ▸ mem_map_of_mem _ cubic_mem, W g x, W g y, ?_⟩
  have he' := congrArg (W g) he
  simpa only [map_add, map_sub, map_mul, Module.End.mul_apply,
    W.self_inv_apply, W.inv_self_apply] using he'
end BinaryLinearThree
