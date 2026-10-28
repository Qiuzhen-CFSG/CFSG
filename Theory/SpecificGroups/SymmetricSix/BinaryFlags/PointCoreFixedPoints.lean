module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# Fixed letters of the even point core

The canonical even point core fixes precisely the distinguished duad `{4,5}`.
Its inclusion in `K` supplies these two fixed letters, while the generator
`(01)(23)` moves all four complementary letters. Conjugation transports this
description to any relabeling of the same core.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Notation 13.2.1 and the exceptional-subgroup argument in §13.5.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The even point core has exactly two fixed letters. -/
theorem pointCoreEven_fixed_iff (x : Fin 6) :
    (∀ p ∈ pointCoreEven, p x = x) ↔ x = 4 ∨ x = 5 := by
  constructor
  · intro h
    have ha : swap01 * swap23 ∈ pointCoreEven := by
      refine ⟨?_, ?_⟩
      · rw [pointCore_eq_closure]
        exact subset_closure (by simp)
      · change Equiv.Perm.sign _ = 1
        decide
    have hc : ∀ y : Fin 6, (swap01 * swap23) y = y → y = 4 ∨ y = 5 := by
      decide
    exact hc x (h _ ha)
  · rintro (rfl | rfl) p hp
    · exact (mem_K.mp (pointCoreEven_le_K hp)).1.1
    · exact (mem_K.mp (pointCoreEven_le_K hp)).1.2

/-- Relabeling transports the two fixed letters of the even point core. -/
theorem conjugate_pointCoreEven_fixed_iff (g : S) (x : Fin 6) :
    (∀ p ∈ pointCoreEven.map (MulAut.conj g).toMonoidHom, p x = x) ↔
      x = g 4 ∨ x = g 5 := by
  constructor
  · intro h
    have hback : ∀ p ∈ pointCoreEven, p (g⁻¹ x) = g⁻¹ x := by
      intro p hp
      have he := congrArg (g⁻¹ : S) (h _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hp))
      change g⁻¹ ((g * p * g⁻¹) x) = g⁻¹ x at he
      simpa only [Equiv.Perm.mul_apply,
        Equiv.Perm.inv_def, Equiv.symm_apply_apply] using he
    rcases (pointCoreEven_fixed_iff _).mp hback with h4 | h5
    · exact Or.inl (by simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using congrArg g h4)
    · exact Or.inr (by simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using congrArg g h5)
  · rintro (rfl | rfl) p ⟨q, hq, rfl⟩
    · have hq4 := (pointCoreEven_fixed_iff 4).mpr (Or.inl rfl) q hq
      change (g * q * g⁻¹) (g 4) = g 4
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hq4]
    · have hq5 := (pointCoreEven_fixed_iff 5).mpr (Or.inr rfl) q hq
      change (g * q * g⁻¹) (g 5) = g 5
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hq5]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags
