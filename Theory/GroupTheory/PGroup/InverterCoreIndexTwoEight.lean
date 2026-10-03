module

public import Theory.GroupTheory.PGroup.IndexTwoEightTransport
public import Theory.SpecificGroups.C4SquareSignSwap
public import Theory.SpecificGroups.C4SquareInverterAutomorphisms

/-!
# Elementary eights in extensions of the C₄-square inverter core

The inverter core has four central elements of square one. In an index-two
extension with central omega subgroup of order two, outside conjugation must
move one of these. Its square is inner. The concrete automorphism-selection
theorem supplies an invariant normal elementary eight, which the transport
theorem makes normal in the whole extension. No separate order or p-group
hypothesis is needed.

Source: the order-64 specialization of Janko–Thompson, Math. Z. 113 (1970),
§§1.3–1.4, printed p.386, used on p.389.
-/

namespace C4SquareSignSwap

private instance : DecidablePred (· ∈ Subgroup.center inverterCore) := fun z =>
  decidable_of_iff (∀ g : inverterCore, g * z = z * g) Subgroup.mem_center_iff.symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The generalized dihedral core has exactly four central elements of square one. -/
public theorem card_inverterCore_central_square_one :
    Nat.card {z : inverterCore // z ∈ Subgroup.center inverterCore ∧ z ^ 2 = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end C4SquareSignSwap

namespace Subgroup

/-- The intrinsic extension conclusion follows from invariant-eight selection
for the concrete inverter core. The order of the ambient group is automatic
from the index and the supplied equivalence. -/
public theorem exists_normal_elementary_eight_of_inverterCore_index_two_of_selection
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (C : Subgroup P) (hindex : C.index = 2)
    (hmodel : Nonempty (C ≃* C4SquareSignSwap.inverterCore))
    (hselect : ∀ f : MulAut C4SquareSignSwap.inverterCore,
      (∃ c : C4SquareSignSwap.inverterCore, ∀ x : C4SquareSignSwap.inverterCore,
        f (f x) = c * x * c⁻¹) →
      (¬ ∀ z : C4SquareSignSwap.inverterCore,
        z ∈ center C4SquareSignSwap.inverterCore → z ^ 2 = 1 → f z = z) →
      ∃ U : Subgroup C4SquareSignSwap.inverterCore,
        U.Normal ∧ IsElementaryAbelian 2 U ∧
          8 ≤ Nat.card U ∧ ∀ u ∈ U, f u ∈ U) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨e⟩ := hmodel
  exact exists_normal_elementary_eight_of_index_two_selection hZ C hindex e
    (by rw [C4SquareSignSwap.card_inverterCore_central_square_one]; omega) hselect

/-- An index-two extension of the C₄-square inverter core with central omega
subgroup of order two contains a normal elementary subgroup of order at least
eight. In particular, this applies to the order-64 extension in
Janko–Thompson §§1.3–1.4; its order follows from the supplied model and index. -/
public theorem exists_normal_elementary_eight_of_inverterCore_index_two
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (C : Subgroup P) (hindex : C.index = 2)
    (hmodel : Nonempty (C ≃* C4SquareSignSwap.inverterCore)) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  exact exists_normal_elementary_eight_of_inverterCore_index_two_of_selection
    hZ C hindex hmodel C4SquareSignSwap.inverterCore_invariant_elementary_eight

end Subgroup
