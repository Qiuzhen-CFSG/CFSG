module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The action data used at the end of Janko's recognition proof

Janko's Sections 7--8 construct a subgroup of index 22 and determine its
permutation character. Section 9 uses that action and the 11:5 and 5:4
normalizers to obtain an explicit permutation group. This file specifies
their shared input without asserting that it exists for the local hypotheses.

`PermutationData` is an actual faithful action, its fixed-point counts,
and three elements with normalizer relations. It contains no isomorphism
to M22 or to Janko's concrete terminal subgroup. The construction of this
data and the subsequent permutation classification are separate obligations.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Sections 7--9, especially pp.16--18,
DOI 10.1016/0021-8693(68)90002-1. The fixed counts are one plus the
displayed degree-21 character. We use left conjugation in the normalizer
relations to agree with Lean's multiplication of permutations; the source
uses right actions. Inverting the source action and its selected elements
gives this convention.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification

universe u

/-- The allowed order and fixed-point pairs in the degree-22 action. -/
@[expose] public def allowedOrderFixedPairs : Finset (ℕ × ℕ) :=
  {(1, 22), (2, 6), (3, 4), (4, 2), (5, 2), (6, 0), (7, 1), (8, 0), (11, 0)}

/-- Concrete action data required by the final permutation argument. -/
public structure PermutationData (G : Type u) [Group G] where
  /-- The action on the cosets of the constructed subgroup of index 22. -/
  rho : G →* Equiv.Perm (Fin 22)
  faithful : Function.Injective rho
  even : ∀ g, rho g ∈ alternatingGroup (Fin 22)
  /-- Both the possible element orders and their exact fixed-point counts. -/
  order_fixed : ∀ g, (orderOf g, (Finset.univ.filter (fun x => rho g x = x)).card) ∈
    allowedOrderFixedPairs
  /-- Generators of the 11:5 and 5:4 normalizers with their shared element. -/
  ell : G
  m : G
  n : G
  ell_order : orderOf ell = 11
  m_order : orderOf m = 5
  n_order : orderOf n = 4
  m_conjugates_ell : m * ell * m⁻¹ = ell ^ 4
  n_conjugates_m : n * m * n⁻¹ = m ^ 2

end Theory.GroupTheory.HeldM22A10.M22Identification
