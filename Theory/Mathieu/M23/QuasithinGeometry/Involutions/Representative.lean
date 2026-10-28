module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Fano
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Generators
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.LowerBound
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.UpperBound

/-!
# An involution representative in M23

The concrete representative and its fixed heptad are certified in `Basic`.
`Fano` gives the induced plane and `Generators` certifies explicit centralizing
elements. The lower bound certifies 2688 distinct products of these elements;
the upper bound determines each centralizer element by its images of a Fano
basis and an exterior point. Together they give the exact centralizer order
inside the concrete design automorphism group M23.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.21, printed p.657 (PDF p.674).
-/

namespace Sporadic.Mathieu.M23Geometry

/-- The representative involution has centralizer of order 2688 in M23. -/
public theorem involutionRepresentative_centralizer_card :
    Nat.card (Subgroup.centralizer ({involutionRepresentative} : Set M23)) = 2688 :=
  Nat.le_antisymm involutionRepresentative_centralizer_card_le
    involutionRepresentative_centralizer_card_lower

/-- M23 contains an involution whose centralizer has order 2688. -/
public theorem exists_involution_centralizer_card :
    ∃ t : M23, orderOf t = 2 ∧
      Nat.card (Subgroup.centralizer ({t} : Set M23)) = 2688 :=
  ⟨involutionRepresentative, involutionRepresentative_order,
    involutionRepresentative_centralizer_card⟩

end Sporadic.Mathieu.M23Geometry
