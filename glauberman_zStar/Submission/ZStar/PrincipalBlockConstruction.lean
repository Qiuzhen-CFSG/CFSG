import Submission.ZStar.BlockPreliminaries
import Submission.ZStar.PrincipalBlock

/-!
# Construction of the ordinary principal congruence block

This file constructs all non-modular fields of `PrincipalTwoBlockData` from
the central-character congruence definition of ordinary `2`-blocks.  The
remaining inputs are precisely the local Brauer-map and section-orthogonality
theorems.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace PrincipalBlockConstruction

open BlockPreliminaries CharacterArgument

attribute [local instance] Fintype.ofFinite

universe u

/-- The constant-one ordinary class function is irreducible. -/
theorem ordinaryPrincipalCharacter_irreducible
    {G : Type u} [Group G] [Finite G] :
    Representation.IsIrreducibleCharacter (ordinaryPrincipalCharacter G) := by
  let T : Representation ℂ G (Fin 1 → ℂ) :=
    Representation.trivial ℂ G (Fin 1 → ℂ)
  constructor
  · refine ⟨1, T, ?_⟩
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    change 1 = T.character g
    simp [T, Representation.character]
  · simp [Representation.classFunctionInner, ordinaryPrincipalCharacter]

/-- The completely constructed ordinary congruence-block data. -/
structure PrincipalCongruenceBlockData
    (G : Type u) [Group G] [Finite G] where
  I : Type
  fintypeI : Fintype I
  decidableEqI : DecidableEq I
  chi : I → Representation.ClassFunction G
  complete : Representation.IsCompleteIrreducibleCharacterFamily chi
  eta : ℂ
  eta_spec : IsPrimitiveRoot eta (Nat.card G)
  primeIdeal : Ideal (Representation.cyclotomicOrder eta)
  primeIdeal_maximal : primeIdeal.IsMaximal
  primeIdeal_liesOverTwo :
    primeIdeal.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
  principal : I
  principal_eq : chi principal = ordinaryPrincipalCharacter G

namespace PrincipalCongruenceBlockData

variable {G : Type u} [Group G] [Finite G]

instance (d : PrincipalCongruenceBlockData G) : Fintype d.I := d.fintypeI

instance (d : PrincipalCongruenceBlockData G) : DecidableEq d.I := d.decidableEqI

/-- The principal ordinary `2`-block, defined by congruence of all central
character values modulo the chosen prime above `2`. -/
def block (d : PrincipalCongruenceBlockData G) : Finset d.I :=
  ordinaryTwoBlock d.eta_spec d.primeIdeal d.chi d.complete.1 d.principal

@[simp] theorem principal_mem (d : PrincipalCongruenceBlockData G) :
    d.principal ∈ d.block := by
  exact base_mem_ordinaryTwoBlock d.eta_spec d.primeIdeal d.chi
    d.complete.1 d.principal

theorem mem_block_iff (d : PrincipalCongruenceBlockData G) (i : d.I) :
    i ∈ d.block ↔
      SameTwoBlock d.eta_spec d.primeIdeal
        (d.chi i) (d.chi d.principal)
        (d.complete.1 i) (d.complete.1 d.principal) := by
  exact mem_ordinaryTwoBlock_iff d.eta_spec d.primeIdeal d.chi
    d.complete.1 d.principal i

theorem two_eq_zero_mod_primeIdeal (d : PrincipalCongruenceBlockData G) :
    Ideal.Quotient.mk d.primeIdeal
      (2 : Representation.cyclotomicOrder d.eta) = 0 :=
  two_eq_zero_mod_liesOver d.primeIdeal d.primeIdeal_liesOverTwo

end PrincipalCongruenceBlockData

/-- The ordinary principal congruence block exists for every finite group. -/
theorem exists_principalCongruenceBlockData
    (G : Type u) [Group G] [Finite G] :
    Nonempty (PrincipalCongruenceBlockData G) := by
  classical
  rcases Representation.classFunction_span_irreducible_characters (G := G) with
    ⟨I, hI, chi, hcomplete, _hspan⟩
  letI : Fintype I := hI
  letI : DecidableEq I := Classical.decEq I
  obtain ⟨principal, hprincipal⟩ :=
    hcomplete.2.1 (ordinaryPrincipalCharacter G)
      ordinaryPrincipalCharacter_irreducible
  let eta : ℂ :=
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (Nat.card G : ℂ))
  have heta : IsPrimitiveRoot eta (Nat.card G) := by
    exact Complex.isPrimitiveRoot_exp (Nat.card G)
      (Nat.card_pos (α := G)).ne'
  obtain ⟨P, hPmax, hPover⟩ := exists_maximalIdeal_above_two heta
  exact ⟨{
    I := I
    fintypeI := hI
    decidableEqI := Classical.decEq I
    chi := chi
    complete := hcomplete
    eta := eta
    eta_spec := heta
    primeIdeal := P
    primeIdeal_maximal := hPmax
    primeIdeal_liesOverTwo := hPover
    principal := principal
    principal_eq := hprincipal }⟩

/-- Adding the two genuinely modular theorems to the constructed
congruence block yields the exact package consumed by the completed ordinary
Z*-argument. -/
def PrincipalCongruenceBlockData.toPrincipalTwoBlockData
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (section_invariance : ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z))
    (orthogonal_one : ∀ s : G, IsInvolution s →
      ∑ i ∈ d.block,
        d.chi i (ConjClasses.mk s) * d.chi i (ConjClasses.mk (1 : G)) = 0) :
    PrincipalTwoBlockData G where
  I := d.I
  fintypeI := d.fintypeI
  decidableEqI := d.decidableEqI
  chi := d.chi
  complete := d.complete
  block := d.block
  principal := d.principal
  principal_mem := d.principal_mem
  principal_eq := d.principal_eq
  section_invariance := section_invariance
  orthogonal_one := orthogonal_one

end PrincipalBlockConstruction

end Submission.ZStar
