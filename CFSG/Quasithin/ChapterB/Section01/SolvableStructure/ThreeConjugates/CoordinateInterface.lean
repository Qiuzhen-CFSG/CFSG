module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.StructureInput
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Reduction
public import Theory.PPrimeCore

/-!
# Coordinate recognition needed after the fixed-space reduction

This is conclusion data for the remaining finite-factor argument, not an
existence assertion. In the reduced group, an order-three subgroup with the
source commutator identity must be one factor's odd core. Its distinct Sylow
conjugates must exhaust the cores of the concrete B.1.8 factors. The stable
image family then generates the entire offender subgroup. The permutation
clause concerns the actual conjugation maps on those factors.

The source reduction in `ImageData` constructs the Sylow subgroup, the order-
three image, relative subnormality, generation and commutator hypotheses.
The remaining coordinate-recognition proof must construct this record; final
assembly in `ThreeConjugates` will lift it through the verified quotient map.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Conclusion data identifying all concrete coordinates with the distinct conjugates. -/
structure CoordinateRecognition (d : SolvableFFStructure ρ) (P : Set (Subgroup G))
    (K S : Subgroup G) where
  index : conjugateFamily K S ≃ Fin d.count
  oddCore_eq : ∀ c : conjugateFamily K S,
    (pPrimeCore 2 (d.factor (index c))).map (d.factor (index c)).subtype = (c : Subgroup G)
  generated_eq : generatedBy P ⊤ = offenderSubgroup ρ
  equivariant : ∀ (s : S) (c c' : conjugateFamily K S),
    (c : Subgroup G).map (MulAut.conj (s : G)).toMonoidHom = (c' : Subgroup G) →
      (d.factor (index c)).map (MulAut.conj (s : G)).toMonoidHom = d.factor (index c')

end CFSG.Quasithin.ChapterB.ThreeConjugates
