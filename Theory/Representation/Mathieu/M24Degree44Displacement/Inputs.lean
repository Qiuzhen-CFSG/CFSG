module

public import Theory.Mathieu.M24.Basic
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.SubrepresentationLattice

/-!
# The order-five calculation needed for degree-44 M₂₄ modules

The fixed-space bound below is an independent representation-theoretic input,
not a proved table entry. It asks only about the actual M₂₄ carrier and its
degree-44 binary modules; it contains no involution-displacement conclusion,
cubic ratio assumption, or module degree catalogue.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, author manuscript p.17.
-/

@[expose] public section
namespace Representation.MathieuM24Degree44
open BinaryOffender Sporadic.Mathieu
universe v

/-- The precise order-five fixed-space bound sufficient for the source argument. -/
def FiveFixedSpaceBound : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M24 V),
    Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 44 →
    ∀ x : M24, orderOf x = 5 → Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) ≤ 8

end Representation.MathieuM24Degree44
