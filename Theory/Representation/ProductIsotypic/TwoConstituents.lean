module
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.QuadraticFourGroup.TensorClassification.FactorIrreducible

/-!
# Reconstructing a product module from two constituents

An irreducible product representation containing an absolutely irreducible
first-factor type is a tensor with its multiplicity representation. Any simple
second-factor type occurring in the original module maps nontrivially to one
multiplicity coordinate. Schur's lemma identifies that multiplicity action,
producing an equivariant tensor decomposition over the original field.

The binary linear-three consumer uses this to construct the tensor marking
excluded in Aschbacher--Smith F.9.18(5ii), printed pp.325--326, in the support
argument of14.6.22, printed p.1038. No tensor marking or semisimplicity of the
original product representation is assumed.
-/

public noncomputable section
open scoped TensorProduct
open Representation QuadraticFourGroup.TensorClassification
namespace Representation.ProductIsotypic
variable {k G H V W E : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup E] [Module k E]

/-- Two occurring simple factor types reconstruct the irreducible product
module when the first type is absolutely irreducible. -/
theorem externalTensor_of_two_constituents
    (ρ : Representation k (G × H) V) [ρ.IsIrreducible]
    (σ : Representation k G W) [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (τ : Representation k H E) [τ.IsIrreducible]
    (f : σ.IntertwiningMap (left ρ)) (hf : f ≠ 0)
    (g : τ.IntertwiningMap (ρ.comp (MonoidHom.inr G H))) (hg : g ≠ 0) :
    Nonempty (ρ.Equiv (externalTensor σ τ)) := by
  obtain ⟨n,μ,⟨b⟩⟩ := exists_externalTensor ρ σ f hf
  let : (externalTensor σ μ).IsIrreducible :=
    (RepEquiv.ofRepresentationEquiv b.symm).irreducible_of_euqiv inferInstance
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : μ.IsIrreducible := irreducible_right_of_externalTensor σ μ
  let c := (_root_.TensorProduct.comm k W (Fin n → k)).trans
    ((_root_.TensorProduct.congr (LinearEquiv.refl k (Fin n → k))
      (Module.finBasis k W).equivFun).trans
        (_root_.TensorProduct.piScalarRight k k (Fin n → k) (Fin (Module.finrank k W))))
  have hc (h : H) (z : W ⊗[k] (Fin n → k)) :
      c (externalTensor σ μ (1,h) z) = fun i => μ h (c z i) := by
    induction z using _root_.TensorProduct.induction_on with
    | zero => simp only [map_zero]; funext i; exact (map_zero (μ h)).symm
    | add z w hz hw =>
      simp only [map_add, hz, hw]
      funext i
      simp only [Pi.add_apply,map_add]
    | tmul w x =>
      change (fun i => ((Module.finBasis k W).equivFun (σ 1 w) i) • μ h x) =
        fun i => μ h (((Module.finBasis k W).equivFun w i) • x)
      simp only [map_one,Module.End.one_apply,map_smul]
  let p (i : Fin (Module.finrank k W)) : τ.IntertwiningMap μ := {
    toLinearMap := (LinearMap.proj i).comp (c.toLinearMap.comp
      (b.toLinearEquiv.toLinearMap.comp g.toLinearMap))
    isIntertwining' h := by
      apply LinearMap.ext
      intro x
      change c (b (g (τ h x))) i = μ h (c (b (g x)) i)
      rw [g.isIntertwining]
      change c (b (ρ (1,h) (g x))) i = μ h (c (b (g x)) i)
      have hb := Representation.IntertwiningMap.isIntertwining ρ
        (externalTensor σ μ) b.toIntertwiningMap (1,h) (g x)
      exact (congrArg (fun z => c z i) hb).trans (congrFun (hc h (b (g x))) i) }
  have hp : ∃ i, p i ≠ 0 := by
    by_contra! hz
    apply hg
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change g x = 0
    apply b.injective
    rw [map_zero]
    apply c.injective
    rw [map_zero]
    funext i
    exact congrArg (fun q : τ.IntertwiningMap μ => q x) (hz i)
  obtain ⟨i,hi⟩ := hp
  let d := (p i).ofBijective ((IsIrreducible.bijective_or_eq_zero (p i)).resolve_right hi)
  exact ⟨b.trans (externalTensorEquiv (Representation.Equiv.refl σ) d.symm)⟩

end Representation.ProductIsotypic
