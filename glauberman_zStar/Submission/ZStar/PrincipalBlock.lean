import Submission.ZStar.BlockArgument
import Submission.ZStar.Induction

/-!
# Minimal principal-2-block interface for the Z*-proof

This file deliberately exposes only the two block-theoretic consequences
used by Glauberman's argument.  It does not add assumptions to the final
theorem: the remaining modular development must construct this package from
Brauer theory.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

universe u

/-- The narrow principal-`2`-block package needed by the completed ordinary
character argument.

The first field is a complete family of ordinary irreducible characters.  The
remaining fields are the local section identity and weak block orthogonality
(Feit IV.4.12 and IV.6.2), specialized to involutions. -/
structure PrincipalTwoBlockData (G : Type u) [Group G] [Finite G] where
  I : Type
  fintypeI : Fintype I
  decidableEqI : DecidableEq I
  chi : I → Representation.ClassFunction G
  complete : Representation.IsCompleteIrreducibleCharacterFamily chi
  block : Finset I
  principal : I
  principal_mem : principal ∈ block
  principal_eq : chi principal = CharacterArgument.ordinaryPrincipalCharacter G
  section_invariance : ∀ i ∈ block, ∀ z : G, IsInvolution z → ∀ v : G,
    v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype →
    chi i (ConjClasses.mk (z * v)) = chi i (ConjClasses.mk z)
  orthogonal_one : ∀ s : G, IsInvolution s →
    ∑ i ∈ block,
      chi i (ConjClasses.mk s) * chi i (ConjClasses.mk (1 : G)) = 0

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
  letI : Fintype hblock.I := hblock.fintypeI
  letI : DecidableEq hblock.I := hblock.decidableEqI
  exact BlockArgument.false_of_principalBlock_section_invariance
    hblock.chi hblock.complete hblock.block hblock.principal
    hblock.principal_mem hblock.principal_eq S t s htI hsI htS hsS hst
    htCentral htWeak htNotCentral hcentralizerProper hproperCentral
    hproperCoreCentral hblock.section_invariance hblock.orthogonal_one

end Submission.ZStar
