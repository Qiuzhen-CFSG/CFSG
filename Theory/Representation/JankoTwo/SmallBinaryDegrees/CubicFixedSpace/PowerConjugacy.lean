module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.Calculations

/-!
# Power conjugation on the actual J₂ generators

Explicit words invert the standard cubic b and square the septic ab. Their
identities are checked on the existing degree-100 permutation tables, using
the carrier's inverse/left-action convention. These are the group inputs to
the Scott-inequality proof of the degree-fourteen cubic fixed-space bound.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16. The permutation data are the ATLAS
J2G1-p100B0 data attributed in the imported GeneratorPair module.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
open Sporadic.LeechRelated.J2 GeneratorPair

private def cubicConjugator : Carrier :=
    a * b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b
    * a * b⁻¹ * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * a

private def septicConjugator : Carrier :=
    b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a
    * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹
    * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b⁻¹

set_option maxRecDepth 20000 in
/-- The literal cubic generator is conjugate in the carrier to its square. -/
theorem exists_conjugator_cubic_square :
    ∃ g : Carrier, g * b * g⁻¹ = b ^ 2 := by
  refine ⟨cubicConjugator, ?_⟩
  apply inclusion_injective
  simp only [cubicConjugator, map_mul, map_inv, map_pow]
  simp only [show inclusion a = tableA from generatorA_eq_table,
    show inclusion b = tableB from generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The literal product ab is conjugate in the carrier to its square. -/
theorem exists_conjugator_septic_square :
    ∃ g : Carrier, g * (a * b) * g⁻¹ = (a * b) ^ 2 := by
  refine ⟨septicConjugator, ?_⟩
  apply inclusion_injective
  simp only [septicConjugator, map_mul, map_inv, map_pow]
  simp only [show inclusion a = tableA from generatorA_eq_table,
    show inclusion b = tableB from generatorB_eq_table]
  decide +kernel

/-- The standard cubic acts nontrivially in every faithful representation. -/
theorem cubic_ne_one : b ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Carrier => inclusion g 0) h
  change generatorB 0 = 0 at hh
  rw [generatorB_eq_table] at hh
  exact (by decide : tableB 0 ≠ 0) hh

end Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
