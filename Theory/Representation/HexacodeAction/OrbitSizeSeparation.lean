module
public import Theory.Representation.HexacodeAction.EvenOrbits
public import Theory.Representation.HexacodeAction.EvenBinaryRecognition
public import Theory.Representation.Quotient

/-!
# Orbit separation for faithful irreducible binary six-spaces of 3.A₆

The proved recognition theorem supplies hexacode coordinates and an
automorphism of the actual acting group. Both are retained when transporting
the two-orbit calculation. A group marking then handles the literal quotient
action in 12.2.2(3g).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.1.3,
printed p.453, and 12.2.16, pp.799–800.
-/

public noncomputable section
open Atlas.Codes
namespace Representation.Hexacode

theorem irreducible_six_orbitCardSeparates
    {W : Type*} [AddCommGroup W] [Module Bit W] [Module.Finite Bit W]
    (ρ : Representation Bit HexEvenAutomorphisms W)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hd : Module.finrank Bit W = 6) : OrbitCardSeparates ρ := by
  obtain ⟨a,e,he⟩ := EvenBinaryRecognition.exists_equivariant ρ hf hi hd
  exact evenAction_orbitCardSeparates.of_intertwining a.toMonoidHom a.surjective e he

theorem marked_irreducible_six_orbitCardSeparates
    {A W : Type*} [Group A] [AddCommGroup W] [Module Bit W] [Module.Finite Bit W]
    (ρ : Representation Bit A W) (e : A ≃* HexEvenAutomorphisms)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hd : Module.finrank Bit W = 6) : OrbitCardSeparates ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  let := hi
  have hs : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hi
  have hfaith : Function.Injective σ := hf.comp e.symm.injective
  apply (irreducible_six_orbitCardSeparates σ hfaith hs hd).of_intertwining
    e.toMonoidHom e.surjective (LinearEquiv.refl _ _)
  intro g v
  change ρ g v = ρ (e.symm (e g)) v
  rw [e.symm_apply_apply]

end Representation.Hexacode
