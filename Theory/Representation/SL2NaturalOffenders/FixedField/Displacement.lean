module
public import Theory.Representation.SL2NaturalOffenders.FixedField.Stabilizer
public import Theory.FieldTheory.QuadraticFrobeniusTrace

/-!
# Displacement onto the fixed natural plane

For an outer involution on a binary natural SL₂ module, the displacement
v ↦ E(v)+v maps onto the fixed plane and has that plane as its kernel.
Simultaneous field alignment reduces surjectivity to the quadratic field
trace. The map respects the action of the fixed actors, so it identifies
the quotient by the fixed plane with the fixed natural module itself.

Source application: Aschbacher–Smith, 6.1.14, printed p.671.
-/

public section
namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The binary displacement of an involution takes values in its fixed plane. -/
@[expose] def displacement (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hi : Function.Involutive E) : (Fin 2 → F) →+ fixedVectors E where
  toFun v := ⟨E v + v, by change E (E v + v) = E v + v; rw [map_add, hi, add_comm]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' v w := by apply Subtype.ext; simp only [map_add, AddSubgroup.coe_add]; abel

@[simp] theorem displacement_apply
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (v : Fin 2 → F) : (displacement E hi v : Fin 2 → F) = E v + v := rfl

variable [CharP F 2]

@[simp] theorem displacement_eq_zero
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (v : Fin 2 → F) : displacement E hi v = 0 ↔ E v = v := by
  rw [Subtype.ext_iff]
  change E v + v = 0 ↔ E v = v
  constructor
  · intro h
    ext i
    exact CharTwo.add_eq_zero.mp (congrFun h i)
  · intro h
    ext i
    exact CharTwo.add_eq_zero.mpr (congrFun h i)

variable [Finite F]

theorem displacement_surjective
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g) :
    Function.Surjective (displacement E hi) := by
  classical
  obtain ⟨σ, hσ, hσi, c, B, _, _, hB⟩ :=
    outer_involution_natural_alignment a E hi he ha ho
  have hne : ∃ x, σ x ≠ x := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  intro v
  have hv (i : Fin 2) : σ (B v i) = B v i := by
    have hh := congrFun (hB v) i
    rw [show E (v : Fin 2 → F) = v from v.property] at hh
    exact hh.symm
  choose w hw using fun i => InvolutiveTrace.exists_trace σ hσi hne (B v i) (hv i)
  refine ⟨B.symm w, ?_⟩
  apply Subtype.ext
  apply B.injective
  change B (E (B.symm w) + B.symm w) = B v
  rw [map_add, hB, B.apply_symm_apply]
  ext i
  exact (add_comm _ _).trans (hw i)

omit [Finite F] [CharP F 2] in
theorem displacement_equivariant
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (g : a.fixedSubgroup) (v : Fin 2 → F) :
    (displacement E hi (g.val.val.mulVec v) : Fin 2 → F) =
      g.val.val.mulVec (displacement E hi v : Fin 2 → F) := by
  change E (g.val.val.mulVec v) + g.val.val.mulVec v = g.val.val.mulVec (E v + v)
  rw [he, (MulAut.mem_fixedSubgroup _ _).mp g.property, Matrix.mulVec_add]
end Representation.SL2NaturalOffenders.FixedField
