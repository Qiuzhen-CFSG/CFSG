module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.Inputs
public import Theory.Representation.SU3.FiveSmallModules

/-!
# Absolute representation inputs for the PSU₃(5) calculation

These independent obligations retain the actual source component and its
central quotient, including the arbitrary Hermitian-form witness. The first
is exhaustive for absolute degrees from 20 through 24. The second calculates the literal
order-seven restriction in those degrees. Neither predicate asserts its own
inhabitation or assumes the requested binary projective displacement bound.

`SmallModules` transports these results through the actual Schur field and
handles all other central lifts by vanishing of their fixed spaces. Final
assembly must discharge both predicates. The absolute degree minimum 20 is
supplied separately by the existing rational extraspecial root geometry and
prime-to-five center-order inputs; it is not part of the first obligation.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- Every faithful absolutely irreducible characteristic-two representation of
the source component of degree between 20 and 24 has degree 20 or 21. -/
def FiveAbsoluteSmallDegreeWindow : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L],
    SourceHypotheses ρ L 5 →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K L U), Function.Injective τ →
      τ.IsAbsolutelyIrreducible → 20 ≤ Module.finrank K U →
      Module.finrank K U ≤ 24 → Module.finrank K U = 20 ∨ Module.finrank K U = 21

/-- On each small absolute module, an actual order-seven element whose
projective image also has order seven has displacement exactly 18. -/
def FiveAbsoluteSevenRestriction : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L],
    SourceHypotheses ρ L 5 → SU3.FiveSmallModules.AbsoluteSevenRestriction.{u, v} L

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
