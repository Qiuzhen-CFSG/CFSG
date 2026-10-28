module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorCartan

/-!
# Full Cartan decomposition from the actual actor

The aligned SL₂ torus is the full Cartan modulo the true panel kernel.
For every element of the source Cartan, the actor construction supplies a
same-action torus element. Their quotient lies in the panel kernel, hence in
the core Cartan. This gives the exact product decomposition needed by the
full U₄ torus construction, without a faithful whole-panel model.

Source: Fong--Seitz II (8.1), p.197 and the characteristic-two Cartan
calculation on pp.201--202. The tensor realization and its field labels remain
separate source hypotheses.
-/

public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure GTwoSource ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable (i : Fin 2)
variable (hV : simpleRemainder Q split i ≤ localKernel Q i)
variable (μ : localGroup Q split i ≃* PSL(2,F))
variable (s : HexagonStructure.RootReflection Q split i)

include hV μ s in
/-- Every source Cartan element is a kernel element times an actor torus element. -/
theorem coreCartan_sup_actorTorus :
    coreCartan Q i ⊔ (alignedTorusHom Q split i hV μ s).range = Q.tits.B ⊓ Q.tits.N := by
  apply le_antisymm
  · apply sup_le inf_le_left
    rintro x ⟨a,rfl⟩
    exact (alignedCartanLift Q split i hV μ s a).property
  intro x hx
  obtain ⟨a,ha⟩ := exists_actorCartanPanelMap_preimage Q split i hV μ s ⟨x,hx⟩
  let hxH : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨x,hx⟩
  let k : ↥(Q.tits.B ⊓ Q.tits.N) :=
    ⟨(hxH : X ⧸ Q.D) * (alignedTorusHom Q split i hV μ s a)⁻¹,
      (Q.tits.B ⊓ Q.tits.N).mul_mem hxH.property
        ((Q.tits.B ⊓ Q.tits.N).inv_mem
          (alignedTorus_mem_cartan Q split i hV μ s a))⟩

  have hk : k ∈ (cartanPanelMap Q i).ker := by
    change cartanPanelMap Q i k = 1
    change cartanPanelMap Q i
      (hxH * (alignedCartanLift Q split i hV μ s a)⁻¹) = 1
    rw [map_mul,map_inv,←ha]
    exact mul_inv_cancel _
  rw [cartanPanelMap_kernel] at hk
  have hkmem : (k : X ⧸ Q.D) ∈ coreCartan Q i := ⟨k.property,hk⟩
  have hm := Subgroup.mul_mem (coreCartan Q i ⊔ (alignedTorusHom Q split i hV μ s).range)
    (mem_sup_left hkmem)
    (mem_sup_right (show alignedTorusHom Q split i hV μ s a ∈
      (alignedTorusHom Q split i hV μ s).range from ⟨a,rfl⟩))
  have he : (k : X ⧸ Q.D) * alignedTorusHom Q split i hV μ s a = x := by
    change ((hxH : X ⧸ Q.D) *
      (alignedTorusHom Q split i hV μ s a)⁻¹) *
      alignedTorusHom Q split i hV μ s a = x
    group
    rfl
  rwa [he] at hm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
