module

public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Transporting a quadratic bound to invariant submodules

The same elementary quadratic actor acts on an invariant submodule, with
no greater fixed codimension. Changing the acting group by an isomorphism
preserves its rank and fixed space. If the submodule action is faithful,
the actor also keeps its rank in the literal action image.

These are the elementary section steps underlying Aschbacher–Smith,
B.1.5(8) and F.9.18(3), printed pp.69–70 and 325.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {D E V : Type*} [Group D] [Group E] [Finite D] [Finite E]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

theorem quadraticRatio_subrepresentation_le_two [FiniteDimensional (ZMod 2) V]
    (J : Subrepresentation ρ) (hq : quadraticRatio ρ ≤ 2) :
    quadraticRatio J.toRepresentation ≤ 2 := by
  obtain ⟨A, hA, ha, hb⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  exact (quadraticRatio_le_two_iff J.toRepresentation).mpr
    ⟨A, hA, quadratic_subrepresentation ρ J ha,
      (fixedCodim_subrepresentation_le ρ J A).trans hb⟩

theorem quadraticRatio_comp_equiv_le_two (e : E ≃* D)
    (hq : quadraticRatio ρ ≤ 2) : quadraticRatio (ρ.comp e.toMonoidHom) ≤ 2 := by
  obtain ⟨A, hA, ha, hb⟩ := (quadraticRatio_le_two_iff ρ).mp hq
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
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨B, hB, ?_, ?_⟩
  · intro a hA b hB v
    exact ha (e a) (he ▸ mem_map_of_mem _ hA)
      (e b) (he ▸ mem_map_of_mem _ hB) v
  · have hf : fixedCodim (ρ.comp e.toMonoidHom) B = fixedCodim ρ A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map, he]
    rwa [hf, hr]

theorem quadraticRatio_image_le_two (hf : Function.Injective ρ)
    (hq : quadraticRatio ρ ≤ 2) : quadraticRatio (imageRepresentation ρ) ≤ 2 := by
  obtain ⟨A, hA, ha, hb⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := by
    intro a _ h
    apply hf
    ext v
    simpa using h v
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨actionSubgroup ρ A, hA.actionSubgroup ρ hfaith, ?_, ?_⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact ha x hx y hy v
  · rwa [fixedCodim_actionSubgroup, actionSubgroup_rank ρ A hfaith]

end Representation.BinaryOffender
