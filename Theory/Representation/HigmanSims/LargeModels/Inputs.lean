module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Trace

/-!
# Finite-field construction inputs for the large HS models

The models of degrees 56, 132, 518 and 1000 can be constructed over the
binary field. The two degree-896 models can be constructed over a finite
characteristic-two field and separated by a trace. A final binary model of
degree 1408 is obtained by restricting the ATLAS HS:2 candidate to HS.
Absolute irreducibility is required on the literal permutation-generated
HS carrier, including for that restriction.

These are construction contracts, not existence assertions. Scalar extension
and the assembly into seven inequivalent models are separate from the finite
calculations. Simplicity may be inherited from the application.

Sources: ATLAS of Finite Group Representations, HS page,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/ , candidates HSG1-f2r56B0,
HSG1-f2r132B0, HSG1-f2r518B0, HSG1-f4r896aB0, HSG1-f4r896bB0,
HSG1-f2r1000B0 and HSd2G1-f2r1408B0. These are candidate data for the
modular saturation proof of the degree calculation used in Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 5.1, preprint p.16. The
low-dimensional part is also recorded in Hiss--Malle, corrected Table 2;
that table only covers degrees at most 250.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels

open Sporadic.LeechRelated.HS

/-- The four distinct degrees with binary HS candidates. -/
def binaryDegree : Fin 4 → ℕ := ![56, 132, 518, 1000]

/-- Four actual absolutely irreducible actions over the binary field. -/
def BinaryModelsExist : Prop :=
  IsSimpleGroup Carrier →
    ∃ ρ : ∀ i, Representation (ZMod 2) Carrier (Fin (binaryDegree i) → ZMod 2),
      ∀ i, (ρ i).IsAbsolutelyIrreducible

/-- The equal-degree pair over a finite field, with a trace witness that
continues to separate the actions under every coefficient embedding. -/
def TraceSeparatedPairExists : Prop :=
  IsSimpleGroup Carrier →
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (ρ₁ ρ₂ : Representation k Carrier (Fin 896 → k)),
      ρ₁.IsAbsolutelyIrreducible ∧ ρ₂.IsAbsolutelyIrreducible ∧
        ∃ g : Carrier,
          LinearMap.trace k _ (ρ₁ g) ≠ LinearMap.trace k _ (ρ₂ g)

/-- A binary action of HS itself in degree 1408. In using the HS:2
candidate, its restriction and its absolute irreducibility must be proved. -/
def RestrictedModelExists : Prop :=
  IsSimpleGroup Carrier →
    ∃ ρ : Representation (ZMod 2) Carrier (Fin 1408 → ZMod 2),
      ρ.IsAbsolutelyIrreducible

end Representation.HigmanSims.LargeModels
