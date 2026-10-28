module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftComparison.Regular
public import Theory.Representation.CyclicDefect.ProjectivePairing

/-!
# Applying the regular comparison to projective pairings

An integral lift has an actual complex representation of the same degree.
Its character agrees with the cyclic-root Brauer value on regular elements,
by descending and reducing the characteristic polynomial. Supplying singular
vanishing then constructs the ordinary model and applies ordinary averaging
to the exact representation `linHom P (ρ.tprod σ)`.

The singular-vanishing premise below is the separate obligation of Feit
IV.2.5; these conditional assembly declarations do not prove it. Together
with that obligation, they implement the positivity step of IV.3.3
(printed pp.145–146), without preservation of invariant dimensions.
-/

public section
noncomputable section

namespace Representation.CyclicDefect

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ} {L : CyclicRootLift K m}
  {Q : Representation K G V}

/-- Assemble the proved regular comparison with the separate singular
vanishing statement for this same coefficient extension. -/
@[expose] def ProjectivePairing.IntegralLift.ordinaryModelOfSingularZero
    (A : ProjectivePairing.IntegralLift L Q) (p : ℕ)
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (hsingular : ∀ g : G, p ∣ orderOf g → A.complexRep.character g = 0) :
    ProjectivePairing.OrdinaryModel p L Q where
  degree := A.degree
  rep := A.complexRep
  regular_eq := A.character_eq_value_of_regular p horder
  singular_zero := hsingular

variable [IsAlgClosed K] [Finite G]
  {W U : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- Apply a supplied integral lift to the literal linear-Hom representation
in the tensor pairing. Only the independent singular-vanishing clause remains
explicit; the regular-character comparison is discharged here. -/
theorem regularPairing_tensor_nat_of_integralLift_of_singular_zero (p : ℕ)
    (L : CyclicRootLift K m)
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (ρ : Representation K G V) (σ : Representation K G W) (P : Representation K G U)
    (A : ProjectivePairing.IntegralLift L (linHom P (ρ.tprod σ)))
    (hsingular : ∀ g : G, p ∣ orderOf g → A.complexRep.character g = 0) :
    ∃ n : ℕ, regularPairing p (fun g => L.value ρ g * L.value σ g) (L.value P) =
      (n : ℂ) :=
  regularPairing_tensor_nat_of_ordinaryModel p L horder ρ σ P
    (A.ordinaryModelOfSingularZero p horder hsingular)

end Representation.CyclicDefect
