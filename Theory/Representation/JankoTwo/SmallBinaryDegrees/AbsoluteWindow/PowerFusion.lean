module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TracePowers
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Checks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage

/-!
# Hall--Janko power fusion and characteristic-two characters

The twenty-one literal representatives satisfy the eighth/thirty-second
power-fusion equation with explicit carrier conjugators. Exhaustive conjugacy
coverage transfers those identities to every element of the degree-100 carrier.
The resulting `powerFusion` theorem discharges the concrete fusion contract.

The representation application `character_four` follows by injectivity of
iterated Frobenius. It holds in every finite dimension, without faithfulness,
irreducibility or finiteness of the characteristic-two field.

Sources: ATLAS `J2G1-p100B0`; Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, p.16, for the upper trace-field application.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow

open Sporadic.LeechRelated.J2
open PowerFusionCertificate

/-- Exhaustive conjugacy coverage completes the concrete power-fusion contract. -/
theorem powerFusion_of_representativeCoverage (hcover : RepresentativeCoverage) :
    PowerFusion := by
  intro g
  obtain ⟨i, hi⟩ := hcover g
  exact powerFusion_of_isConj_representative i hi

/-- The eighth and thirty-second powers of every element are conjugate inside
the literal Hall--Janko carrier. Exhaustive coverage is fully discharged. -/
theorem powerFusion : PowerFusion :=
  powerFusion_of_representativeCoverage representativeCoverage

/-- Every characteristic-two character is fixed by fourth powering on each
checked representative's conjugacy class. -/
theorem character_four_of_isConj_representative
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (τ : Representation K Carrier U) (g : Carrier)
    (i : Fin 21) (h : IsConj (representative i) g) :
    τ.character g ^ 4 = τ.character g := by
  exact character_four_of_power_fusion τ g 3
    (by simpa using powerFusion_of_isConj_representative i h)

/-- The trace-field conclusion already holds for every checked representative. -/
theorem character_four_representative
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (τ : Representation K Carrier U) (i : Fin 21) :
    τ.character (representative i) ^ 4 = τ.character (representative i) :=
  character_four_of_isConj_representative τ _ i (IsConj.refl _)

/-- Exhaustive coverage supplies the upper trace-field clause in every dimension. -/
theorem character_four_of_representativeCoverage (hcover : RepresentativeCoverage)
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (τ : Representation K Carrier U) (g : Carrier) :
    τ.character g ^ 4 = τ.character g := by
  exact character_four_of_power_fusion τ g 3
    (by simpa using powerFusion_of_representativeCoverage hcover g)

/-- Every characteristic-two character value of the literal Hall--Janko carrier
is fixed by fourth powering. This proves the upper trace-field clause without
degree-completeness or irreducibility premises. -/
theorem character_four
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (τ : Representation K Carrier U) (g : Carrier) :
    τ.character g ^ 4 = τ.character g := by
  exact character_four_of_power_fusion τ g 3 (by simpa using powerFusion g)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
