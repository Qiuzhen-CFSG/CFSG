module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.LocalInertia
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Combinatorics

/-!
# Assembly of cyclic column incidence on actual modular decomposition data

Apply the finite column and connectivity lemmas to the exact multiplicities
in `Decomposition`. This retains the originally supplied simple modules and
projective columns and constructs the endpoints rather than postulating them.

The current assembly exposes the two still-required source assertions:
squared column norm two (Feit VII.2.13--15 at exceptional multiplicity one),
and indecomposability of the block decomposition matrix (I.17.9). The simple
count VII.2.1 is also a separate source obligation. This conditional reduction
is not the cyclic-defect existence theorem.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m}

/-- Construct the endpoints and their connected graph from the two precise
matrix assertions, retaining the literal decomposition numbers. -/
theorem incidence_of_column_squares_and_crossing (a : Decomposition d residue L n)
    (hsq : ∀ e, ∑ v : {i // i ∈ d.block}, a.multiplicity v e ^ 2 = 2)
    (hcross : ∀ S : Finset {i // i ∈ d.block}, S.Nonempty → S ≠ Finset.univ →
      ∃ e v w, v ∈ S ∧ w ∉ S ∧ a.multiplicity v e ≠ 0 ∧ a.multiplicity w e ≠ 0) :
    Nonempty (Incidence a) := by
  let : Nonempty {i // i ∈ d.block} := ⟨⟨d.principal, d.principal_mem⟩⟩
  have he (e : Fin n) := exists_endpoints_of_sum_sq_eq_two
    (fun v => a.multiplicity v e) (hsq e)
  choose left right hne hmul using he
  exact ⟨{
    left := left
    right := right
    endpoints_ne := hne
    multiplicity_eq := fun v e => by
      by_cases hv : v = left e ∨ v = right e
      · simpa only [if_pos hv] using hmul e v
      · simpa only [if_neg hv] using hmul e v
    connected := endpointGraph_connected_of_crossing a.multiplicity left right hne
      (fun v e => hmul e v) hcross }⟩

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
