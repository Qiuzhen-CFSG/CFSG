module

public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Involutions centralizing the residual of a symmetric-three square

An element of square one in S₃×S₃ centralizing A₃×A₃ is the identity.
Each coordinate centralizes a cubic cycle, whose centralizer contains no
involution. The coordinate calculation is checked in S₃ and transports
through any actual group equivalence.

Source application: faithfulness of Rc* on the extraspecial Y* in
Aschbacher--Smith15.2.3(1)(ii), printed p.1105.
-/

namespace SymmetricThreeProductResidual
open Subgroup

private theorem coordinate_eq_one : ∀ r : Equiv.Perm (Fin 3), r ^ 2 = 1 →
    (∀ y ∈ alternatingGroup (Fin 3), r * y = y * r) → r = 1 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- A square-one element centralizing the full residual is trivial. -/
public theorem eq_one_of_square_of_centralizes_residual
    {D : Type*} [Group D]
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (r : D) (hr : r ^ 2 = 1)
    (hc : ∀ y ∈ pResidual 2 D, r * y = y * r) : r = 1 := by
  have hs : (e r) ^ 2 = 1 := by rw [← map_pow, hr, map_one]
  have hcomm : ∀ z ∈ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)),
      e r * z = z * e r := by
    intro z hz
    have hzm : z ∈ (pResidual 2 D).map e.toMonoidHom := by
      rw [map_pResidual 2 e, residual_eq]
      exact hz
    obtain ⟨y, hy, rfl⟩ := hzm
    exact (e.map_mul r y).symm.trans ((congrArg e (hc y hy)).trans (e.map_mul y r))
  apply e.injective
  rw [map_one]
  apply Prod.ext
  · apply coordinate_eq_one (e r).1 (congrArg Prod.fst hs)
    intro y hy
    exact congrArg Prod.fst (hcomm (y, 1) ⟨hy, one_mem _⟩)
  · apply coordinate_eq_one (e r).2 (congrArg Prod.snd hs)
    intro y hy
    exact congrArg Prod.snd (hcomm (1, y) ⟨one_mem _, hy⟩)

end SymmetricThreeProductResidual
