module
public import Theory.SpecificGroups.Monster.Construction.LocalC.Descent

/-!
# The exact kernel of the spin–Leech tensor map

Trivial tensor action forces trivial extraspecial conjugation and hence
trivial binary Leech action. The proved Leech kernel leaves only identity
or lattice negation. Contracting one natural coordinate determines the
spin factor in each case: both factors have the same sign. Conversely
these paired signs act identically on the tensor product.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 148–149,
and the tensor product construction of Section 6.
-/

public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

local instance : AddCommGroup SpinSpace := inferInstance

/-- The two factors in the tensor kernel have the same scalar sign. -/
theorem pullbackTensor_kernel_iff (p : localPullback) : pullbackTensor p = 1 ↔
    (p.val.2 = 1 ∧ ∀ v, p.val.1.val.1 v = v) ∨
      (p.val.2 = negationIsometry ∧ ∀ v, p.val.1.val.1 v = -v) := by
  constructor
  · intro hp
    have hg := (leechModTwoRepresentation_kernel p.val.2).mp
      (pullbackTensor_kernel_modTwo p hp)
    have ht (v : SpinSpace) : pullbackTensor p (Pi.single 0 1 ⊗ₜ[ℝ] v) =
        Pi.single 0 1 ⊗ₜ[ℝ] v := congrArg (fun f : MinusSpace ≃ₗ[ℝ] MinusSpace =>
          f (Pi.single 0 1 ⊗ₜ[ℝ] v)) hp
    rcases hg with hg | hg
    · left
      refine ⟨hg,fun v => ?_⟩
      have h := ht v
      rw [pullbackTensor_tmul, hg, map_one] at h
      have hc := congrArg firstContraction h
      rw [firstContraction_tmul, firstContraction_tmul] at hc
      change (1 : ℝ) • p.val.1.val.1 v = (1 : ℝ) • v at hc
      simpa only [one_smul] using hc
    · right
      refine ⟨hg,fun v => ?_⟩
      have h := ht v
      rw [pullbackTensor_tmul, hg, realLeechRepresentation_negation] at h
      have hc := congrArg firstContraction h
      rw [firstContraction_tmul, firstContraction_tmul] at hc
      change (- (1 : ℝ)) • p.val.1.val.1 v = (1 : ℝ) • v at hc
      have hn : (- (1 : ℝ)) • p.val.1.val.1 v = -(p.val.1.val.1 v) := by
        exact (neg_smul (1 : ℝ) _).trans (congrArg Neg.neg (one_smul ℝ _))
      rw [hn, one_smul] at hc
      simpa only [neg_neg] using congrArg Neg.neg hc
  · rintro (⟨hg,hf⟩ | ⟨hg,hf⟩)
    · apply LinearEquiv.toLinearMap_injective
      apply TensorProduct.ext'
      intro a b
      change pullbackTensor p (a ⊗ₜ[ℝ] b) = a ⊗ₜ[ℝ] b
      rw [pullbackTensor_tmul, hg, map_one, hf]
      rfl
    · apply LinearEquiv.toLinearMap_injective
      apply TensorProduct.ext'
      intro a b
      change pullbackTensor p (a ⊗ₜ[ℝ] b) = a ⊗ₜ[ℝ] b
      rw [pullbackTensor_tmul, hg, realLeechRepresentation_negation, hf]
      change (-a) ⊗ₜ[ℝ] (-b) = a ⊗ₜ[ℝ] b
      simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

end Sporadic.Monster.Construction.LocalC
