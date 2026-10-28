module

public import Theory.Representation.BinaryNaturalDual.NaturalIsotypicExclusion
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# Transport for the binary natural-plus-dual `SL₃(2)` action

The matrix model `BinaryLinearThree.Group` and the linear-automorphism model
`BinaryLinear.OuterCyclic.LinearGroup 3` are identified by the literal
`slEquivLinear 3`.  This file records the coordinate action comparison and
the resulting transport of marked linear representations. Conjugating an
arbitrary actor automorphism by this equivalence transfers the binary
natural-copy exclusion. A surjective marking then gives the exclusion on
the original module and its original action.

Source: supporting action transport for Aschbacher–Smith, combined manuscript
(1 March 2004), C.4.8. The exclusion is the natural-isotypic calculation used
in 12.1.9(1), printed p.793, via 4.4.3(i.a), printed p.619. This file proves
the transport and exclusion, not the C.4.8 classification or its orthogonal
alternative. The action comparison follows the coordinate conventions in
`Theory/Representation/PSL3Two/NaturalDualCentralizer.lean`.
-/

@[expose] public section

open Representation
open BinaryLinear BinaryLinear.OuterCyclic

namespace BinaryLinearThree.NaturalDual

/-- The literal matrix natural-plus-dual action agrees with the
`BinaryLinear.GL` natural-dual action after the actor equivalence. -/
theorem naturalDualRepresentation_slEquivLinear (g : BinaryLinearThree.Group) :
    BinaryNaturalDual.naturalDualRepresentation
        (BinaryLinear.OuterCyclic.slEquivLinear 3 g) =
      BinaryLinearThree.NaturalDual.action g := by
  apply LinearMap.ext
  intro v
  rw [BinaryNaturalDual.naturalDualRepresentation_apply]
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro w
    change v.2 ((BinaryLinear.OuterCyclic.slEquivLinear 3 g)⁻¹ w) = _
    rw [← map_inv]
    rfl

/-- An actual marked representation equivalence transports through the
literal actor homomorphism into the linear-automorphism model. -/
noncomputable def representationEquiv_of_action
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (q : D →* BinaryLinearThree.Group)
    (e : V ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (he : ∀ g v, e (ρ g v) =
      BinaryLinearThree.NaturalDual.action (q g) (e v)) :
    ρ.Equiv
      (BinaryNaturalDual.naturalDualRepresentation.comp
        ((BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp q)) := by
  apply Representation.Equiv.mk e
  intro g
  apply LinearMap.ext
  intro v
  change e (ρ g v) =
    BinaryNaturalDual.naturalDualRepresentation
      (BinaryLinear.OuterCyclic.slEquivLinear 3 (q g)) (e v)
  rw [naturalDualRepresentation_slEquivLinear]
  exact he g v

/-- Equation-level form of `representationEquiv_of_action`, useful for
source coordinate records whose actor is given as a monoid homomorphism. -/
theorem transport_action_equation
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (q : D →* BinaryLinearThree.Group)
    (e : V ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (he : ∀ g v, e (ρ g v) =
      BinaryLinearThree.NaturalDual.action (q g) (e v))
    (g : D) (v : V) :
    e (ρ g v) =
      BinaryNaturalDual.naturalDualRepresentation
        (((BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp q) g)
        (e v) := by
  change e (ρ g v) =
    BinaryNaturalDual.naturalDualRepresentation
      (BinaryLinear.OuterCyclic.slEquivLinear 3 (q g)) (e v)
  rw [naturalDualRepresentation_slEquivLinear]
  exact he g v

/-- Transport of an arbitrary actor automorphism retains its value on each
marked matrix actor. -/
theorem automorphism_slEquivLinear
    (a : MulAut BinaryLinearThree.Group) (g : BinaryLinearThree.Group) :
    MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3) a
        (BinaryLinear.OuterCyclic.slEquivLinear 3 g) =
      BinaryLinear.OuterCyclic.slEquivLinear 3 (a g) := by
  change BinaryLinear.OuterCyclic.slEquivLinear 3
    (a ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm
      (BinaryLinear.OuterCyclic.slEquivLinear 3 g))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Changing the actor model also transports any automorphism used to mark
the natural-plus-dual action; the linear coordinates remain the supplied map. -/
theorem transport_twisted_action_equation
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (q : D →* BinaryLinearThree.Group) (a : MulAut BinaryLinearThree.Group)
    (e : V ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (he : ∀ g v, e (ρ g v) =
      BinaryLinearThree.NaturalDual.action (a (q g)) (e v))
    (g : D) (v : V) :
    e (ρ g v) = BinaryNaturalDual.naturalDualRepresentation
      (((MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3) a).toMonoidHom.comp
        ((BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp q)) g) (e v) := by
  change e (ρ g v) = BinaryNaturalDual.naturalDualRepresentation
    (MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3) a
      (BinaryLinear.OuterCyclic.slEquivLinear 3 (q g))) (e v)
  rw [automorphism_slEquivLinear, naturalDualRepresentation_slEquivLinear]
  exact he g v

/-- The six-dimensional binary natural-plus-dual action cannot be marked as
repeated copies of the natural action, even after an arbitrary actor
automorphism. -/
theorem no_repeated_natural_equiv
    {ι : Type*} [Fintype ι]
    (a : MulAut BinaryLinearThree.Group)
    (e : BinaryLinearThree.NaturalDual.Space ≃ₗ[ZMod 2]
      (ι → BinaryLinearThree.Vector))
    (he : ∀ g v, e (BinaryLinearThree.NaturalDual.action g v) =
      fun i => BinaryLinearThree.W (a g) (e v i)) : False := by
  apply BinaryNaturalDual.no_natural_copies_equiv (n := 3) (by decide)
    (MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3) a) e
  intro g v
  obtain ⟨g, rfl⟩ := (BinaryLinear.OuterCyclic.slEquivLinear 3).surjective g
  rw [naturalDualRepresentation_slEquivLinear, automorphism_slEquivLinear]
  exact he g v

/-- The exclusion on an original module with a surjective actor marking.
It compares the actual two coordinate maps for that same source action. -/
theorem no_repeated_natural_equiv_of_surjective
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (q : D →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : V ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (he : ∀ g v, e (ρ g v) = BinaryLinearThree.NaturalDual.action (q g) (e v))
    {ι : Type*} [Fintype ι] (a : MulAut BinaryLinearThree.Group)
    (f : V ≃ₗ[ZMod 2] (ι → BinaryLinearThree.Vector))
    (hf : ∀ g v, f (ρ g v) = fun i => BinaryLinearThree.W (a (q g)) (f v i)) :
    False := by
  apply no_repeated_natural_equiv a (e.symm.trans f)
  intro g v
  obtain ⟨g, rfl⟩ := hq g
  obtain ⟨v, rfl⟩ := e.surjective v
  simp only [LinearEquiv.trans_apply, ← he, LinearEquiv.symm_apply_apply]
  exact hf g v

end BinaryLinearThree.NaturalDual
