module

public import CFSG.Quasithin.ClassicalModels
public import Theory.Representation.HexacodeAction.Cover
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-!+# Concrete perfect actors in B.5.6

The single-actor alternatives use the literal classical matrix groups, the
split-octonion G₂ model, alternating groups, and the even hexacode triple
cover. Every constructor includes an actual multiplicative equivalence.
The two-factor alternatives have the smaller PSL₂ / PSL₃ catalogue, with
the odd field-degree restriction from B.5.6(3). The SL₃(2) and PSL₂ factors
in (5) occur in this same smaller catalogue.

These are group presentations, not classification assertions. Quasisimplicity
is an inherited branch hypothesis. Neither module equivalence nor existence
of an element of order three is asserted by these definitions. Compatible
representations and the natural, double-natural, indecomposable, or hyperplane
module data must still accompany the presentation at final case assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
B.5.6, printed pp.99 and 105; A.3.5 for the triple-cover convention.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting

/-- The actual group possibilities when the B.5.6 actor equals its
quasisimple generalized Fitting subgroup. -/
inductive PerfectActorModel (X : Type*) [Group X] : Prop
  | linear_two (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (lower : 2 ≤ n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
  | linear_three (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (positive : 0 < n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) F))
  | symplectic_four (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (lower : 2 ≤ n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Matrix.symplecticGroup (Fin 2) F))
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (lower : 2 ≤ n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Atlas.G2.Model F))
  | alternating_six (equiv : Nonempty (X ≃* alternatingGroup (Fin 6)))
  | alternating_seven (equiv : Nonempty (X ≃* alternatingGroup (Fin 7)))
  | triple_cover (equiv : Nonempty (X ≃* Atlas.Codes.HexEvenAutomorphisms))
  | g2_derived (equiv : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | binary_linear (n : ℕ) (lower : 4 ≤ n) (upper : n ≤ 5)
      (equiv : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))

/-- The perfect factors allowed in the product alternatives (3) and (5).
The excluded degree-one PSL₂ is S₃ and belongs to the separate solvable work. -/
inductive PerfectFactorModel (X : Type*) [Group X] : Prop
  | linear_two (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (lower : 2 ≤ n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
  | linear_three (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (positive : 0 < n) (odd : Odd n) (card : Nat.card F = 2 ^ n)
      (equiv : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
