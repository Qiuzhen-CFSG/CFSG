module

public import Theory.GroupTheory.ZStar.PrincipalBlockData
public import Theory.GroupTheory.ZStar.BlockArgument
public import Theory.GroupTheory.ZStar.Induction
public import Theory.GroupTheory.ZStar.MinimalSteps

/-!
# Closing the principal two-block minimal counterexample

The principal two-block package, together with the precise smaller-group
induction hypothesis, makes a central weakly closed Sylow involution central
in a group with trivial odd core.

Assuming noncentrality, the minimal-counterexample reductions supply a second
Sylow involution, proper involution centralizers, and centrality modulo the odd
core in every proper subgroup containing the distinguished involution.
Local isolation gives odd commutator orders. These are exactly the elementary
and inductive inputs to the principal-block contradiction; the package supplies
its two modular character identities.

This is the theorem portion of historical
`Submission/ZStar/PrincipalBlock.lean` at commit `c3503435`.
The package is re-exported from PrincipalBlockData so modular construction
does not depend on this induction theorem. No additional hypotheses are added.
Source: G. Glauberman, “Central elements in core-free groups”,
J. Algebra 4 (1966).
-/

public section
noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar
open BenderSuzuki.PFAppendixIII
universe u

/-- Once the minimal principal-block package is available, the core-free
minimal-counterexample step is completely formal. -/
theorem central_of_principalTwoBlockData_and_induction
    {G : Type u} [Group G] [Finite G]
    (hblock : PrincipalTwoBlockData G)
    (hIH : OddOrderZStarInductionHypothesis G)
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ x, x ∈ (S : Subgroup G) → x * t = t * x)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    t ∈ Subgroup.center G := by
  classical
  by_contra htNotCentral
  have hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)) :=
    orderOf_commutator_odd_of_weaklyClosed S t htI htCentral htWeak
  obtain ⟨s, hsS, hsI, hst⟩ :=
    exists_second_involution_of_not_central_corefree
      hcore S t htI htS htNotCentral
  have hcentralizerProper : ∀ z : G, IsInvolution z →
      Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro z hzI
    exact involutionCentralizer_ne_top_of_induction
      hIH hcore t htI htNotCentral hodd z hzI
  have hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n := by
    intro N hNnormal hNproper htN
    exact properNormal_central_of_induction
      hIH hcore t htI hodd N hNnormal hNproper htN
  have hproperCoreCentral : ∀ (H : Subgroup G), H ≠ ⊤ → t ∈ H →
      ∀ h : G, h ∈ H →
        h * t * h⁻¹ * t⁻¹ ∈ (pPrimeCore 2 H).map H.subtype := by
    intro H hHproper htH
    exact properSubgroup_commutators_mem_pPrimeCore_of_induction
      hIH t htI hodd H hHproper htH
  let : Fintype hblock.I := hblock.fintypeI
  let : DecidableEq hblock.I := hblock.decidableEqI
  exact BlockArgument.false_of_principalBlock_section_invariance
    hblock.chi hblock.complete hblock.block hblock.principal
    hblock.principal_mem hblock.principal_eq S t s htI hsI htS hsS hst
    htCentral htWeak htNotCentral hcentralizerProper hproperCentral
    hproperCoreCentral hblock.section_invariance hblock.orthogonal_one

end Glauberman.ZStar


