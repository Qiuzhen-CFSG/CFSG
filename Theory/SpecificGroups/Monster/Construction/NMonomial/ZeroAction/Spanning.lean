module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Coordinates

/-!
# Spanning tests for the three literal zero summands

The marked coordinate basis and the signed axis vectors span each tensor
space. The actual odd short vectors span the odd summand by its published
definition. Together these give an extensionality test for linear maps out
of `ZeroSpace`, in precisely the generators used by 29.6--29.9.

Source: Aschbacher, *Sporadic Groups*, 29.1(4), 29.8 and the standard basis
paragraph on printed p. 157. No linear independence of the redundant signed
families is assumed.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem tensorTwo_ext (f g : TensorTwo →ₗ[ℝ] M)
    (h : ∀ x b, f (pointVector x ⊗ₜ[ℝ] delta2 b) =
      g (pointVector x ⊗ₜ[ℝ] delta2 b)) : f = g := by
  apply TensorProduct.ext
  apply (Pi.basisFun ℝ (Fin 24)).ext
  intro i
  apply firstSecond.geometry.vector_ext
  intro a
  obtain ⟨b,rfl⟩ := axis2Equiv.surjective a
  rw [Pi.basisFun_apply]
  change f (Pi.single i 1 ⊗ₜ[ℝ] delta2 b) = g (Pi.single i 1 ⊗ₜ[ℝ] delta2 b)
  simpa only [pointVector, coordinateMarking.symm_apply_apply] using h (coordinateMarking i) b

theorem tensorThree_ext (f g : TensorThree →ₗ[ℝ] M)
    (h : ∀ x b, f (pointVector x ⊗ₜ[ℝ] delta3 b) =
      g (pointVector x ⊗ₜ[ℝ] delta3 b)) : f = g := by
  apply TensorProduct.ext
  apply (Pi.basisFun ℝ (Fin 24)).ext
  intro i
  apply firstThird.geometry.vector_ext
  intro a
  obtain ⟨b,rfl⟩ := axis3Equiv.surjective a
  rw [Pi.basisFun_apply]
  change f (Pi.single i 1 ⊗ₜ[ℝ] delta3 b) = g (Pi.single i 1 ⊗ₜ[ℝ] delta3 b)
  simpa only [pointVector, coordinateMarking.symm_apply_apply] using h (coordinateMarking i) b

theorem oddSpace_ext (f g : oddSpace →ₗ[ℝ] M)
    (h : ∀ x b, f (zeroOdd x b).1 = g (zeroOdd x b).1) : f = g := by
  apply LinearMap.ext
  intro v
  obtain ⟨v,hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨⟨x,b⟩,rfl⟩ := ha
    exact h x b
  | zero => exact (map_zero f).trans (map_zero g).symm
  | add a b ha hb ha' hb' =>
    change f (⟨a,ha⟩ + ⟨b,hb⟩) = g (⟨a,ha⟩ + ⟨b,hb⟩)
    rw [map_add,map_add,ha',hb']
  | smul c a ha ha' =>
    change f (c • ⟨a,ha⟩) = g (c • ⟨a,ha⟩)
    rw [map_smul,map_smul,ha']

/-- The three literal marked families determine every linear map out of B_0. -/
theorem zeroSpace_ext (f g : ZeroSpace →ₗ[ℝ] M)
    (ho : ∀ x b, f (zeroOdd x b) = g (zeroOdd x b))
    (ht : ∀ x b, f (zeroTwo (pointVector x) (delta2 b)) =
      g (zeroTwo (pointVector x) (delta2 b)))
    (hh : ∀ x b, f (zeroThree (pointVector x) (delta3 b)) =
      g (zeroThree (pointVector x) (delta3 b))) : f = g := by
  have h1 : f.comp (LinearMap.inl ℝ oddSpace (TensorTwo × TensorThree)) =
      g.comp (LinearMap.inl ℝ oddSpace (TensorTwo × TensorThree)) := by
    apply oddSpace_ext
    exact ho
  have h2 : f.comp ((LinearMap.inr ℝ oddSpace (TensorTwo × TensorThree)).comp
      (LinearMap.inl ℝ TensorTwo TensorThree)) =
      g.comp ((LinearMap.inr ℝ oddSpace (TensorTwo × TensorThree)).comp
        (LinearMap.inl ℝ TensorTwo TensorThree)) := by
    apply tensorTwo_ext
    exact ht
  have h3 : f.comp ((LinearMap.inr ℝ oddSpace (TensorTwo × TensorThree)).comp
      (LinearMap.inr ℝ TensorTwo TensorThree)) =
      g.comp ((LinearMap.inr ℝ oddSpace (TensorTwo × TensorThree)).comp
        (LinearMap.inr ℝ TensorTwo TensorThree)) := by
    apply tensorThree_ext
    exact hh
  apply LinearMap.ext
  intro v
  have hv : v = (v.1,0) + (0,v.2.1,0) + (0,0,v.2.2) := by simp
  rw [hv, map_add, map_add, map_add, map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (LinearMap.congr_fun h1 v.1) (LinearMap.congr_fun h2 v.2.1))
    (LinearMap.congr_fun h3 v.2.2)

end Sporadic.Monster.Construction.NMonomial.ZeroAction
