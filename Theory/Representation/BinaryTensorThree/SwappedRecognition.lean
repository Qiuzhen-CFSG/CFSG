module
public import Theory.Representation.BinaryTensorThree.Recognition
public import Theory.Representation.PSL3Two.IrreducibleCatalogue

/-!
# Recognizing an exchanged irreducible binary linear-three square

The first factor has a nontrivial irreducible constituent. The actual exchange
carries its inclusion to a second-factor inclusion of the same type. The checked
SL₃(2) catalogue and absolute irreducibility then reconstruct the whole product
module from these two maps. The natural and dual-natural types give the literal
nine-dimensional tensor action; the other alternative is the actual Steinberg
tensor square. No dimension, tensor decomposition or action-image premise is used.

The original Chapter10 selected-module consumer retains this distinction before
applying its ambient tensor exclusion. Source: Aschbacher--Smith D.3.7 and
H.6.1, printed pp.197--199,386; original3.2.6(2), printed p.581.
-/

public noncomputable section
open Representation Representation.ProductIsotypic
open Representation.QuadraticFourGroup.TensorClassification
namespace BinaryTensorThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private def exchangedMap
    (ρ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group) V)
    (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (ρ (g,1) v) = ρ (1,g) (E v))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (f : σ.IntertwiningMap (left ρ)) :
    σ.IntertwiningMap (ρ.comp (MonoidHom.inr _ _)) := {
  toLinearMap := E.toLinearMap.comp f.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change E (f (σ g v)) = ρ (1,g) (E (f v))
    rw [f.isIntertwining]
    exact hE g (f v) }

omit [FiniteDimensional (ZMod 2) V] in
private theorem exchangedMap_ne_zero
    (ρ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group) V)
    (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (ρ (g,1) v) = ρ (1,g) (E v))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (f : σ.IntertwiningMap (left ρ)) (hf : f ≠ 0) : exchangedMap ρ E hE σ f ≠ 0 := by
  intro hz
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change f v = 0
  apply E.injective
  rw [map_zero]
  exact congrArg (fun q : σ.IntertwiningMap (ρ.comp (MonoidHom.inr _ _)) => q v) hz

/-- An irreducible exchanged binary linear-three square is the natural tensor
or the actual Steinberg tensor square. The dual natural type is absorbed by
its genuine graph automorphism. -/
theorem exchanged_irreducible_alternatives
    (ρ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group) V)
    [ρ.IsIrreducible] (hleft : ∃ g, ρ (g,1) ≠ 1)
    (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (ρ (g,1) v) = ρ (1,g) (E v)) :
    (∃ e : (BinaryLinearThree.Group × BinaryLinearThree.Group) ≃* (Factor × Factor),
      Nonempty (ρ.Equiv (baseRepresentation.comp e.toMonoidHom))) ∨
      Nonempty (ρ.Equiv (externalTensor BinaryLinearThree.S BinaryLinearThree.S)) := by
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
    obtain ⟨g,hg⟩ := hleft
    apply hg
    apply LinearMap.ext
    intro v
    apply c.injective
    change c (ρ (g,1) v) = c v
    rw [hc]
    funext i
    exact hz g (c v i)
  have hmap {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
      {σ : Representation (ZMod 2) BinaryLinearThree.Group W}
      (b : U.toRepresentation.Equiv σ) : inc.comp b.symm.toIntertwiningMap ≠ 0 := by
    intro hz
    apply hi
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun f : σ.IntertwiningMap (left ρ) => f (b v)) hz
    change inc (b.toLinearEquiv.symm (b.toLinearEquiv v)) = 0 at hh
    change inc v = 0
    simpa only [b.toLinearEquiv.symm_apply_apply] using hh
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial U.toRepresentation hmove with
    hb | hb | hb
  · obtain ⟨b⟩ := hb
    let f := inc.comp b.symm.toIntertwiningMap
    exact Or.inl (exists_marking_of_natural_factor_maps ρ (MulEquiv.refl _) (MulEquiv.refl _)
      f (hmap b) (exchangedMap ρ E hE _ f) (exchangedMap_ne_zero ρ E hE _ f (hmap b)))
  · obtain ⟨b⟩ := hb
    let b' := b.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm
    let f := inc.comp b'.symm.toIntertwiningMap
    exact Or.inl (exists_marking_of_natural_factor_maps ρ
      BinaryLinearThree.AutomorphismAction.graph BinaryLinearThree.AutomorphismAction.graph
      f (hmap b') (exchangedMap ρ E hE _ f) (exchangedMap_ne_zero ρ E hE _ f (hmap b')))
  · obtain ⟨b⟩ := hb
    let f := inc.comp b.symm.toIntertwiningMap
    let := BinaryLinearThree.IrreducibleCatalogue.steinberg_absolute
    let := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible BinaryLinearThree.S
    exact Or.inr (externalTensor_of_two_constituents ρ BinaryLinearThree.S BinaryLinearThree.S
      f (hmap b) (exchangedMap ρ E hE _ f) (exchangedMap_ne_zero ρ E hE _ f (hmap b)))
end BinaryTensorThree
