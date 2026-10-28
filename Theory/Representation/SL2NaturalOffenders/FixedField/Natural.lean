module
public import Theory.Representation.SL2NaturalOffenders.FixedField.Alignment
public import Theory.Representation.SL2NaturalOffenders.FixedField.Extraction

/-!
# The fixed natural module of an outer involution

Apply the simultaneous actor/vector alignment and restrict both coordinate
changes to their literal fixed subgroups. The resulting group is SL₂ over the
actual fixed subfield, and its action on the actual fixed natural plane is the
natural action under the same marking. This closes the module-descent input
in Aschbacher--Smith, Lemma 2.4.12(2), without a residual semilinearity or
compatibility assumption.
-/

public section
noncomputable section
namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The literal fixed natural plane is invariant under the literal fixed actors. -/
theorem fixed_action_mem_of_intertwines
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (g : a.fixedSubgroup) (v : fixedVectors E) :
    g.val.val.mulVec (v : Fin 2 → F) ∈ fixedVectors E := by
  change E (g.val.val.mulVec (v : Fin 2 → F)) = g.val.val.mulVec (v : Fin 2 → F)
  rw [he, (show E (v : Fin 2 → F) = v from v.property),
    (MulAut.mem_fixedSubgroup _ _).mp g.property]

variable [Finite F] [CharP F 2]

/-- The actual fixed actors and fixed natural plane form the natural SL₂ module
over the same fixed field. There is no remaining compatibility premise. -/
theorem outer_involution_fixed_natural
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃ eActor : a.fixedSubgroup ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ),
      ∃ eV : fixedVectors E ≃+ (Fin 2 → FixedBy.subfield F σ),
        ∀ (g : a.fixedSubgroup) (v : fixedVectors E),
          eV ⟨g.val.val.mulVec (v : Fin 2 → F), fixed_action_mem_of_intertwines a E he g v⟩ =
            (eActor g).val.mulVec (eV v) := by
  obtain ⟨σ, hne, hs, c, B, hnat, hβ, hB⟩ :=
    outer_involution_natural_alignment a E hi he ha houter
  let B₂ := B.restrictScalars (ZMod 2)
  refine ⟨σ, hne, hs, fixedActorEquiv a σ (MulAut.conj c⁻¹) hβ,
    fixedVectorEquiv σ E B₂ hB, ?_⟩
  intro g v
  exact fixed_equivariance a σ (MulAut.conj c⁻¹) E B₂ hβ hB hnat g v
end Representation.SL2NaturalOffenders.FixedField
