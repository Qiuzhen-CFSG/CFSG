module
public import Theory.Representation.SL2NaturalOffenders.FixedField.Natural

/-!
# Stabilizing the fixed plane of an outer involution

The square of an additive intertwiner of an involutory SL₂ automorphism is
scalar. A nonzero fixed vector forces that scalar to be one. Simultaneous
field alignment then shows that the matrices preserving its fixed plane are
exactly the fixed actors: the fixed plane contains a basis of the original
field vector space.

This is the linear-algebra step in Aschbacher--Smith, 6.1.14, printed p.671.
The ambient group element need not itself be an involution.
-/

public section
namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- A nonzero fixed vector removes the scalar ambiguity in the square. -/
theorem intertwiner_involutive_of_fixed
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (hv : ∃ v, v ≠ 0 ∧ E v = v) :
    Function.Involutive E := by
  have haa (g) : a (a g) = g := congrArg (fun b : MulAut _ => b g) ha
  obtain ⟨c, hc⟩ := centralizer_scalar
    (E.toAddMonoidHom.comp E.toAddMonoidHom) (by
      intro g v
      change E (E (g.val.mulVec v)) = g.val.mulVec (E (E v))
      rw [he, he, haa])
  obtain ⟨v, hv, hEv⟩ := hv
  have hcv : c • v = v := (hc v).symm.trans (by change E (E v) = v; rw [hEv, hEv])
  have hc1 : c = 1 := (smul_left_injective F hv) (hcv.trans (one_smul F v).symm)
  intro v
  simpa [hc1] using hc v

variable [Finite F] [CharP F 2]

/-- A matrix preserves the outer involution's fixed plane precisely when it
is fixed by the same quotient actor. -/
theorem preserves_fixed_iff
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g)
    (g : SpecialLinearGroup (Fin 2) F) :
    (∀ v, E v = v → E (g.val.mulVec v) = g.val.mulVec v) ↔ a g = g := by
  constructor
  · intro hg
    obtain ⟨σ, _, _, c, B, hnat, hβ, hB⟩ :=
      outer_involution_natural_alignment a E hi he ha ho
    apply (MulAut.conj c⁻¹).injective
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    let v : Fin 2 → F := B.symm (Pi.single j 1)
    have hv : E v = v := by
      apply B.injective
      rw [hB]
      change (fun k => σ (B (B.symm (Pi.single j 1)) k)) = B (B.symm (Pi.single j 1))
      simp only [B.apply_symm_apply]
      ext k
      by_cases hk : k = j <;> simp [hk]
    have hh : (a g).val.mulVec v = g.val.mulVec v := by
      have hh := hg v hv
      rwa [he, hv] at hh
    have hh' := congrArg B hh
    rw [hnat, hnat] at hh'
    have hBv : B v = Pi.single j 1 := B.apply_symm_apply _
    rw [hBv, Matrix.mulVec_single, Matrix.mulVec_single] at hh'
    simpa using congrFun hh' i
  · intro hg v hv
    rw [he, hg, hv]
end Representation.SL2NaturalOffenders.FixedField
