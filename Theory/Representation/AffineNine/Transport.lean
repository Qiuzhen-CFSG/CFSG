module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Cubic-ratio transport across the actual affine model isomorphism

The source action on `H/C_H(W)` is compared with the concrete affine model by
a genuine group equivalence. The cubic actor, fixed codimension and rank are
transported together, preserving the threshold-two statement.
-/

public section

open scoped ENNReal
open Subgroup
namespace Representation.BinaryOffender
variable {D E V W : Type*} [Group D] [Group E] [Finite D] [Finite E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (rho : Representation (ZMod 2) D V)

theorem cubicRatio_comp_equiv_le_two (e : E ≃* D)
    (hq : cubicRatio rho ≤ 2) : cubicRatio (rho.comp e.toMonoidHom) ≤ 2 := by
  obtain ⟨A, hA, hc, hb⟩ := (cubicRatio_le_nat_iff rho 2).mp hq
  let B := A.map e.symm.toMonoidHom
  have he : B.map e.toMonoidHom = A := by
    rw [map_map]
    simp
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro h
    exact hA.1 (by rw [← he, h, Subgroup.map_bot])
  have hr : rank B = rank A := by
    rw [← rank_map_injective e.toMonoidHom e.injective, he]
  have hcB : IsCubic (rho.comp e.toMonoidHom) B := by
    intro a ha b hb c hc' v
    exact hc (e a) (he ▸ mem_map_of_mem _ ha)
      (e b) (he ▸ mem_map_of_mem _ hb) (e c) (he ▸ mem_map_of_mem _ hc') v
  have hfixed : fixedCodim (rho.comp e.toMonoidHom) B = fixedCodim rho A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, he]
  apply (cubicRatio_le_nat_iff _ 2).mpr
  exact ⟨B, hB, hcB, hfixed ▸ hr ▸ hb⟩
end Representation.BinaryOffender
