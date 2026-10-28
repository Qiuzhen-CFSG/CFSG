module

public import Theory.Representation.PrimeFixedPointCentralization.MinimalStructure
public import Theory.Representation.PrimeFixedPointCentralization.Branches
public import Theory.Representation.PrimeFixedPointCentralization.Reduction

/-!
# Fixed vectors for faithful actions of distinct odd primes

In the minimal faithful irreducible case, the representation makes the kernel's
center cyclic. The resulting abelian or extraspecial structural alternative
gives a nonzero actor-fixed vector. The faithful-image and subgroup induction
then removes irreducibility and minimality.

This assembles Aschbacher, *Finite Group Theory*, second edition, 36.2,
printed p.194, for binary modules and distinct odd primes. The Fermat-prime
exception does not occur in this domain. It supplies the fixed-vector input
used in Aschbacher–Smith A.1.12, printed p.22.
-/

universe u
namespace Representation.PrimeFixedPointCentralization

/-- The minimal faithful irreducible fixed-vector statement, with its
structural alternative derived from the given representation. -/
public theorem minimal_fixed_vectors
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hqodd : Odd q) (hrodd : Odd r) (hqr : q ≠ r) :
    MinimalFixedVectorStatement.{u} q r := by
  intro P A W _ _ _ _ _ _ _ hP hA φ hφ hmin ρ hirr hfaith
  let : ρ.IsIrreducible := hirr
  exact fixed_vector_of_structure hqodd hrodd hqr hP hA φ hφ
    (hasMinimalActionStructure_of_faithful_irreducible hqodd hrodd hP hA hqr
      φ hφ hmin ρ hfaith) ρ hfaith

/-- A faithful action of a group of odd prime order on a group of a distinct
odd prime-power order has a nonzero actor-fixed vector in every faithful
finite-dimensional binary representation of its semidirect product. -/
public theorem prime_action_fixed_vectors
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hqodd : Odd q) (hrodd : Odd r) (hqr : q ≠ r) :
    PrimeActionFixedVectorStatement.{u} q r :=
  prime_action_fixed_vectors_of_minimal hqodd hrodd hqr
    (minimal_fixed_vectors hqodd hrodd hqr)

end Representation.PrimeFixedPointCentralization
