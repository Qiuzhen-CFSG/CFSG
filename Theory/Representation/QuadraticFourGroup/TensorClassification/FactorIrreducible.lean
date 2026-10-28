module
public import Theory.Representation.QuadraticFourGroup.TensorClassification.FixedPoints
public import Theory.Representation.RepEquiv
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
/-!
# Irreducibility descends to an external tensor factor

A nonzero invariant subspace of the right factor gives a nonzero tensor
subrepresentation. Irreducibility makes its inclusion surjective; faithful
flatness of the nonzero left vector space descends surjectivity. The actual
consumer is the multiplicity representation in the binary deleted branch
of Aschbacher–Smith D.3.7, printed pp.197–199.
-/
public section
open scoped TensorProduct
open Representation
namespace Representation.QuadraticFourGroup.TensorClassification
variable {k G H U W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [Nontrivial U]
  [AddCommGroup W] [Module k W]
  (σ : Representation k G U) (μ : Representation k H W)
  [(externalTensor σ μ).IsIrreducible]

include σ in
theorem irreducible_right_of_externalTensor : μ.IsIrreducible := by
  let : Nontrivial (U ⊗[k] W) := Subrepresentation.irreducible_module_nontrivial (externalTensor σ μ)
  let : Nontrivial W := (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := k) (M := U)).mp inferInstance
  rw [IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let j : (externalTensor σ S.toRepresentation).IntertwiningMap (externalTensor σ μ) := {
    toLinearMap := S.toSubmodule.subtype.lTensor U
    isIntertwining' g := by ext u w; rfl }
  have hj : j ≠ 0 := by
    have hn : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
    let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
    obtain ⟨w,hw0⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one k hu
    intro hz
    have he := congrArg (fun f : (externalTensor σ S.toRepresentation).IntertwiningMap
      (externalTensor σ μ) => f (u ⊗ₜ[k] w)) hz
    change u ⊗ₜ[k] (w : W) = 0 at he
    have hc := congrArg (fun x : U ⊗[k] W => _root_.TensorProduct.lid k W (l.rTensor W x)) he
    exact hw0 (Subtype.ext (by simpa [hl] using hc))
  have hsurj := (IsIrreducible.surjective_or_eq_zero j).resolve_right hj
  have hs : Function.Surjective S.toSubmodule.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k U S.toSubmodule.subtype).mp hsurj
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  obtain ⟨v,hv⟩ := hs w
  exact hv ▸ v.property
end Representation.QuadraticFourGroup.TensorClassification
