module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements

/-!+# The concrete central diagonal in the contrary-fusion argument

This is the geometric output immediately before the central-quotient step
on printed p.95. It records an actual conjugator exchanging the factors,
their order-two intersection, and an order-four element whose product with
its conjugate is a central involution. It assumes no quotient setup or
conclusion. The intersecting-case argument must construct this data; the
quotient argument must eliminate it in a minimal counterexample.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the paragraph ending “Thus y ∈ Z(G)”.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup

/-- The source's actual central diagonal, with right-conjugation conventions. -/
structure CentralDiagonal {G : Type*} [Group G] (A₁ A₂ : Subgroup G) (t : G) : Prop where
  swaps : conjugate A₁ t = A₂
  intersection_card : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2
  diagonal : ∃ u ∈ A₁, orderOf u = 4 ∧
    orderOf (u * (t⁻¹ * u * t)) = 2 ∧ u * (t⁻¹ * u * t) ∈ center G

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
