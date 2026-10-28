module
public import Theory.Representation.PSL3Two.ProductCatalogue
public import Theory.Representation.BinaryTensorThree.Recognition

/-!
# Natural coordinates in the binary linear-three product catalogue

The natural and dual types on either factor have actual matrix-tensor
coordinates, with independent graph twists. The product catalogue therefore
constructs this marking below degree24; the bound only eliminates its
Steinberg types. No coordinates are inferred from the dimension alone.

Source: Aschbacher--Smith D.3.7 and H.6.1, printed pp.197--199,386.
The original Chapter10 seed is the consumer in ModuleChoice.QuietSeedTensor.
-/

public noncomputable section
open Representation Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace BinaryLinearThree.ProductCatalogue

private theorem natural_factor_marking (a : FactorType) (ha : a ≠ .steinberg) :
    ∃ e : MulAut Group, Nonempty (a.action.Equiv (W.comp e.toMonoidHom)) := by
  cases a with
  | natural => exact ⟨1,⟨Representation.Equiv.refl W⟩⟩
  | dual => exact ⟨AutomorphismAction.graph,⟨AutomorphismAction.graphNaturalDual.symm⟩⟩
  | steinberg => exact False.elim (ha rfl)

/-- Every marked tensor whose factors are natural or dual has the actual
binary matrix-tensor coordinates, with independent factor twists. -/
theorem natural_tensor_marking (a b : FactorType)
    (ha : a ≠ .steinberg) (hb : b ≠ .steinberg) :
    ∃ e : (Group × Group) ≃* (BinaryTensorThree.Factor × BinaryTensorThree.Factor),
      Nonempty ((externalTensor a.action b.action).Equiv
        (BinaryTensorThree.baseRepresentation.comp e.toMonoidHom)) := by
  obtain ⟨ea,⟨ca⟩⟩ := natural_factor_marking a ha
  obtain ⟨eb,⟨cb⟩⟩ := natural_factor_marking b hb
  let σ := W.comp ea.toMonoidHom
  let τ := W.comp eb.toMonoidHom
  let c := BinaryLinear.OuterCyclic.slEquivLinear 3
  let e := (ea.trans c).prodCongr (eb.trans c)
  let d : (externalTensor σ τ).Equiv
      (BinaryTensorThree.baseRepresentation.comp e.toMonoidHom) :=
    .mk BinaryTensorThree.coordinates (by
      intro x
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simpa only [LinearMap.comp_apply,map_add] using congrArg₂ (· + ·) hz hw
      | tmul u v =>
        change BinaryTensorThree.coordinates (σ x.1 u ⊗ₜ[ZMod 2] τ x.2 v) =
          BinaryTensorThree.baseAction (e x) (BinaryTensorThree.coordinates (u ⊗ₜ[ZMod 2] v))
        rw [BinaryTensorThree.baseAction_tmul]
        rfl)
  exact ⟨e,⟨(externalTensorEquiv ca cb).trans d⟩⟩

/-- Below degree24 the product catalogue gives genuine natural tensor
coordinates; the degree is used only to exclude the marked Steinberg types. -/
theorem natural_tensor_marking_of_degree_lt_twentyFour
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (Group × Group) V)
    (a b : FactorType) (c : σ.Equiv (externalTensor a.action b.action))
    (hd : Module.finrank (ZMod 2) V < 24) :
    ∃ e : (Group × Group) ≃* (BinaryTensorThree.Factor × BinaryTensorThree.Factor),
      Nonempty (σ.Equiv (BinaryTensorThree.baseRepresentation.comp e.toMonoidHom)) := by
  rw [finrank_of_marking σ a b c] at hd
  have ha : a ≠ .steinberg := by
    intro he
    subst a
    cases b <;> simp [FactorType.degree] at hd
  have hb : b ≠ .steinberg := by
    intro he
    subst b
    cases a <;> simp [FactorType.degree] at hd
  obtain ⟨e,⟨d⟩⟩ := natural_tensor_marking a b ha hb
  exact ⟨e,⟨c.trans d⟩⟩
end BinaryLinearThree.ProductCatalogue
