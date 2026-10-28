module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.ProductIsotypic.TwoConstituents
public import Theory.Representation.Quotient

/-!
# The nontrivial binary SL₃ square catalogue

The checked SL₃(2) catalogue gives a natural, dual-natural or Steinberg
constituent on each moving factor of an irreducible product module. Absolute
irreducibility reconstructs the original representation as their external
tensor, with the two factor labels unchanged. Thus the nine actual marked
models have dimensions 9, 24 or 64; dimension is a consequence of recognition.

The original proper-seed application is in Chapter10's QuietSeed module.
Source: Aschbacher--Smith H.6.1 and D.3.5--7, printed pp.386 and195--199.
-/

public noncomputable section
open Representation Representation.ProductIsotypic
open Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace BinaryLinearThree.ProductCatalogue

/-- The three nontrivial simple types, each with its concrete representation. -/
inductive FactorType
  | natural | dual | steinberg

abbrev FactorType.Carrier : FactorType → Type
  | .natural => Vector
  | .dual => Module.Dual (ZMod 2) Vector
  | .steinberg => Steinberg

instance (a : FactorType) : AddCommGroup a.Carrier :=
  match a with
  | .natural => inferInstance
  | .dual => inferInstance
  | .steinberg => inferInstance
instance (a : FactorType) : Module (ZMod 2) a.Carrier :=
  match a with
  | .natural => inferInstance
  | .dual => inferInstance
  | .steinberg => inferInstance
instance (a : FactorType) : FiniteDimensional (ZMod 2) a.Carrier :=
  match a with
  | .natural => inferInstance
  | .dual => inferInstance
  | .steinberg => inferInstance

@[expose] def FactorType.action (a : FactorType) : Representation (ZMod 2) Group a.Carrier :=
  match a with
  | .natural => W
  | .dual => W.dual
  | .steinberg => S

instance (a : FactorType) : a.action.IsAbsolutelyIrreducible := by
  cases a
  · exact IrreducibleCatalogue.natural_absolute
  · exact IrreducibleCatalogue.dual_absolute
  · exact IrreducibleCatalogue.steinberg_absolute

instance (a : FactorType) : a.action.IsIrreducible :=
  IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible a.action

@[expose] def FactorType.degree : FactorType → ℕ
  | .natural | .dual => 3
  | .steinberg => 8

theorem FactorType.finrank (a : FactorType) : Module.finrank (ZMod 2) a.Carrier = a.degree := by
  cases a
  · change Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3
    simp
  · change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 3
    rw [Subspace.dual_finrank_eq]
    simp
  · exact finrank_steinberg

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem model_map
    (ρ : Representation (ZMod 2) (Group × Group) V) [ρ.IsIrreducible]
    (hm : ∃ g, ρ (g,1) ≠ 1) :
    ∃ a : FactorType, ∃ f : a.action.IntertwiningMap (left ρ), f ≠ 0 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (left ρ)
  let := hU
  let inc : U.toRepresentation.IntertwiningMap (left ρ) :=
    .mk U.toSubmodule.subtype (fun _ => rfl)
  have hi : inc ≠ 0 := by
    let : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : U.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg (fun f : U.toRepresentation.IntertwiningMap (left ρ) => f v) hz))
  have hmove : ∃ g v, U.toRepresentation g v ≠ v := by
    by_contra! hz
    obtain ⟨n,c,hc⟩ := exists_copy_coordinates ρ U.toRepresentation inc hi
    obtain ⟨g,hg⟩ := hm
    apply hg
    apply LinearMap.ext
    intro v
    apply c.injective
    change c (ρ (g,1) v) = c v
    rw [hc]
    funext i
    exact hz g (c v i)
  have hmap (a : FactorType) (b : U.toRepresentation.Equiv a.action) :
      inc.comp b.symm.toIntertwiningMap ≠ 0 := by
    intro hz
    apply hi
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun f : a.action.IntertwiningMap (left ρ) => f (b v)) hz
    change inc (b.toLinearEquiv.symm (b.toLinearEquiv v)) = 0 at hh
    change inc v = 0
    simpa only [b.toLinearEquiv.symm_apply_apply] using hh
  rcases IrreducibleCatalogue.classify_nontrivial U.toRepresentation hmove with hb | hb | hb
  · obtain ⟨b⟩ := hb
    exact ⟨.natural,inc.comp b.symm.toIntertwiningMap,hmap .natural b⟩
  · obtain ⟨b⟩ := hb
    exact ⟨.dual,inc.comp b.symm.toIntertwiningMap,hmap .dual b⟩
  · obtain ⟨b⟩ := hb
    exact ⟨.steinberg,inc.comp b.symm.toIntertwiningMap,hmap .steinberg b⟩

/-- Both original moving factors determine an actual external tensor marking. -/
theorem classify_moving_product
    (ρ : Representation (ZMod 2) (Group × Group) V) [ρ.IsIrreducible]
    (hl : ∃ g, ρ (g,1) ≠ 1) (hr : ∃ g, ρ (1,g) ≠ 1) :
    ∃ a b : FactorType, Nonempty (ρ.Equiv (externalTensor a.action b.action)) := by
  obtain ⟨a,f,hf⟩ := model_map ρ hl
  let c : (Group × Group) ≃* (Group × Group) := MulEquiv.prodComm
  let τ : Representation (ZMod 2) (Group × Group) V := ρ.comp c.toMonoidHom
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff c.toMonoidHom c.surjective ρ).mpr inferInstance
  obtain ⟨b,g,hg⟩ := model_map τ hr
  exact ⟨a,b,externalTensor_of_two_constituents ρ a.action b.action f hf g hg⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- The dimension of the original space follows from its equivariant marking. -/
theorem finrank_of_marking
    (ρ : Representation (ZMod 2) (Group × Group) V) (a b : FactorType)
    (e : ρ.Equiv (externalTensor a.action b.action)) :
    Module.finrank (ZMod 2) V = a.degree * b.degree := by
  rw [e.toLinearEquiv.finrank_eq,Module.finrank_tensorProduct,a.finrank,b.finrank]

/-- All possible degrees when both factors act nontrivially. -/
theorem degree_cases
    (ρ : Representation (ZMod 2) (Group × Group) V) [ρ.IsIrreducible]
    (hl : ∃ g, ρ (g,1) ≠ 1) (hr : ∃ g, ρ (1,g) ≠ 1) :
    Module.finrank (ZMod 2) V = 9 ∨ Module.finrank (ZMod 2) V = 24 ∨
      Module.finrank (ZMod 2) V = 64 := by
  obtain ⟨a,b,⟨e⟩⟩ := classify_moving_product ρ hl hr
  rw [finrank_of_marking ρ a b e]
  cases a <;> cases b <;> simp [FactorType.degree]

end BinaryLinearThree.ProductCatalogue
