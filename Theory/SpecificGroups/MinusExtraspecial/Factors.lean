module

public import Theory.SpecificGroups.MinusExtraspecial.Model
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Transporting the quaternion–dihedral factors

An actual isomorphism with the concrete minus extraspecial model supplies
commuting quaternion and dihedral subgroups generating the original group.
The subgroups are the ranges of the transported model embeddings.

Source: the central-product description in Aschbacher–Smith, I.4.7,
printed p.418. This interface is used by the five-point involution action.
-/

namespace MinusExtraspecial

/-- The concrete model equivalence supplies actual internal central-product factors. -/
public theorem factors_of_equiv {Q : Type*} [Group Q] (e : Q ≃* Model) :
    ∃ B C : Subgroup Q, Nonempty (B ≃* QuaternionGroup 2) ∧
      Nonempty (C ≃* DihedralGroup 4) ∧
      C ≤ Subgroup.centralizer (B : Set Q) ∧ B ⊔ C = ⊤ := by
  let b := e.symm.toMonoidHom.comp quaternion
  let c := e.symm.toMonoidHom.comp dihedral
  refine ⟨b.range, c.range,
    ⟨(MonoidHom.ofInjective (e.symm.injective.comp quaternion_injective)).symm⟩,
    ⟨(MonoidHom.ofInjective (e.symm.injective.comp dihedral_injective)).symm⟩, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩ _ ⟨q, rfl⟩
    exact ((factors_commute q d).map e.symm).eq
  · apply top_unique
    intro x _
    obtain ⟨q, d, h⟩ := factors_generate (e x)
    have hx : b q * c d = x := by
      simpa only [b, c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm h
    rw [← hx]
    exact Subgroup.mul_mem_sup ⟨q, rfl⟩ ⟨d, rfl⟩

end MinusExtraspecial
