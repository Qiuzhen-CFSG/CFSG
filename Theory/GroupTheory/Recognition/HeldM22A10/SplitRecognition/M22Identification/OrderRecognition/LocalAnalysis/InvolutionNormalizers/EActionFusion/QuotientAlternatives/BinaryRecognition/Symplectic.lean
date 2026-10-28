module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.BinaryRecognition.Forms
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The distinguished form stabilizer embeds in the actual symplectic group

An explicit linear basis change carries the form with matrix J+I on four
binary coordinates to `Matrix.J` on two hyperbolic pairs. Conjugating an
automorphism preserving the former form therefore gives a symplectic matrix.
The resulting homomorphism is injective because the basis change is invertible.

This constructs the concrete model comparison used for Janko,
“A characterization of the Mathieu simple groups, I”, J. Algebra 9 (1968),
Section 2, Lemma 6, p.6.
-/

@[expose] public section

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Matrix
namespace Theory.GroupTheory.HeldM22A10.BinaryRecognition

abbrev W := (Fin 2 ⊕ Fin 2) → ZMod 2

def basisChange : V ≃ₗ[ZMod 2] W where
  toFun v := Sum.elim ![v 0 + v 2 + v 3, v 2] ![v 1 + v 2 + v 3, v 3]
  invFun v := ![v (.inl 0) + v (.inl 1) + v (.inr 1),
    v (.inr 0) + v (.inl 1) + v (.inr 1), v (.inl 1), v (.inr 1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

set_option maxRecDepth 10000 in
theorem basisChange_form : ∀ v w : V,
    (Matrix.J (Fin 2) (ZMod 2)).toBilin' (basisChange v) (basisChange w) =
      standard v w := by
  decide +kernel

def formStabilizer := MulAction.stabilizer (MulAut BinaryFour) base

def conjugateLinear (g : formStabilizer) : W ≃ₗ[ZMod 2] W :=
  (basisChange.symm.trans (linear g.val)).trans basisChange

theorem conjugate_preserves (g : formStabilizer) (v w : W) :
    (Matrix.J (Fin 2) (ZMod 2)).toBilin' (conjugateLinear g v) (conjugateLinear g w) =
      (Matrix.J (Fin 2) (ZMod 2)).toBilin' v w := by
  change (Matrix.J (Fin 2) (ZMod 2)).toBilin'
    (basisChange (linear g.val (basisChange.symm v)))
    (basisChange (linear g.val (basisChange.symm w))) = _
  rw [basisChange_form]
  have h := (action_eq_iff g.val base).mp g.property
  change ∀ v w : V, standard (linear g.val v) (linear g.val w) = standard v w at h
  rw [h, ← basisChange_form]
  simp

def stabilizerRepresentation : formStabilizer →* Matrix.symplecticGroup (Fin 2) (ZMod 2) where
  toFun g := ⟨(conjugateLinear g).toLinearMap.toMatrix', by
    rw [SymplecticGroup.mem_iff']
    have hf : (Matrix.J (Fin 2) (ZMod 2)).toBilin'.comp
        (conjugateLinear g).toLinearMap (conjugateLinear g).toLinearMap =
          (Matrix.J (Fin 2) (ZMod 2)).toBilin' := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact conjugate_preserves g v w
    have hm := congrArg LinearMap.BilinForm.toMatrix' hf
    rw [LinearMap.BilinForm.toMatrix'_comp] at hm
    simpa only [LinearMap.BilinForm.toMatrix'_toBilin'] using hm⟩
  map_one' := by
    apply Subtype.ext
    change (conjugateLinear 1).toLinearMap.toMatrix' = 1
    have h : (conjugateLinear 1).toLinearMap = 1 := by
      apply LinearMap.ext
      intro v
      change basisChange (basisChange.symm v) = v
      exact basisChange.apply_symm_apply v
    rw [h, LinearMap.toMatrix'_one]
  map_mul' g h := by
    apply Subtype.ext
    change (conjugateLinear (g * h)).toLinearMap.toMatrix' =
      (conjugateLinear g).toLinearMap.toMatrix' * (conjugateLinear h).toLinearMap.toMatrix'
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    apply LinearMap.ext
    intro v
    change basisChange (linear g.val (linear h.val (basisChange.symm v))) =
      basisChange (linear g.val (basisChange.symm
        (basisChange (linear h.val (basisChange.symm v)))))
    rw [basisChange.symm_apply_apply]

theorem stabilizerRepresentation_injective : Function.Injective stabilizerRepresentation := by
  intro g h heq
  have hm := congrArg Subtype.val heq
  change (conjugateLinear g).toLinearMap.toMatrix' =
    (conjugateLinear h).toLinearMap.toMatrix' at hm
  have hl := LinearMap.toMatrix'.injective hm
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  have hv := congrArg (fun f : W →ₗ[ZMod 2] W => f (basisChange v.toAdd)) hl
  change basisChange (linear g.val (basisChange.symm (basisChange v.toAdd))) =
    basisChange (linear h.val (basisChange.symm (basisChange v.toAdd))) at hv
  have hv' : linear g.val v.toAdd = linear h.val v.toAdd := by
    simpa only [basisChange.symm_apply_apply, basisChange.injective.eq_iff] using hv
  exact congrArg Multiplicative.ofAdd hv'

end Theory.GroupTheory.HeldM22A10.BinaryRecognition
