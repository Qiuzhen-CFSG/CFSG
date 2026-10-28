module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cardinality of roots of unity in a finite field

If a positive integer n divides |F|-1, the n-th roots of unity in the finite
field F have cardinality n. A generator of the cyclic unit group, raised
to its order divided by n, is a primitive n-th root. The primitive-root
cardinality theorem gives the result.

This is the common field-theory calculation for the actual scalar subgroups
of GL2 and GU2 in Alperin--Brauer--Gorenstein II.2 Lemma 1(v), article
pp17–18. It is independent of matrix models and requires no parity assumption.
-/

namespace FiniteField

public theorem card_rootsOfUnity_of_dvd (F : Type*) [Field F] [Finite F]
    (n : ℕ) [NeZero n] (hd : n ∣ Nat.card F - 1) :
    Nat.card (rootsOfUnity n F) = n := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hd' : n ∣ orderOf a := by simpa [ha, Nat.card_units] using hd
  have ha0 : orderOf a ≠ 0 := orderOf_pos a |>.ne'
  have hp : IsPrimitiveRoot (a ^ (orderOf a / n)) n :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_pow_orderOf_div ha0 hd')
  exact hp.card_rootsOfUnity'

end FiniteField
