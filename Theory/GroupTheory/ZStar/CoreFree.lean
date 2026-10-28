module

public import Theory.GroupTheory.ZStar.CoreFreeAssembly
public import Theory.GroupTheory.ZStar.PrincipalBlockFactory

/-!
# The core-free Z-star theorem

In a finite group with trivial odd core, a weakly closed involution central
in a Sylow two-subgroup is central in the whole group. The unconditional
principal-block factory supplies the section-invariance and orthogonality
data required by the proved strong-induction assembly. That assembly uses
the ordinary-character contradiction in a minimal counterexample.

This is the exact core-free endpoint of
`Submission/ZStar/CoreFree.lean` at revision `c3503435`. The proof uses the
actual uniform block factory, not a hypothesis asserting block existence.
The general odd-core quotient reduction is the subsequent public assembly.
Source: G. Glauberman, “Central elements in core-free groups”,
J. Algebra 4 (1966).
-/

public section
namespace Glauberman.ZStar
open BenderSuzuki.PFAppendixIII

/-- A Sylow-central weakly closed involution is central when the odd core is trivial. -/
theorem glauberman_zstar_corefree
    {G : Type*} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G)
    (htI : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    t ∈ Subgroup.center G := by
  exact glauberman_zstar_corefree_of_exists_principalTwoBlockData
    PrincipalBlockFactory.principalTwoBlockData_factory
    hcore S t htI htS htCentral htWeak

end Glauberman.ZStar
