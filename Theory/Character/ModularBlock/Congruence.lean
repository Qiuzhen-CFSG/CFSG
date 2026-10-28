module

public import Theory.Character.ModularBlock.CentralCharacter

/-!
# Construction of the ordinary principal congruence block

For any finite group, choose a complete family of complex irreducible
characters, its principal character, a primitive root of unity of order
`|G|`, and a maximal ideal of the cyclotomic integer ring above two. The
ordinary principal block is the congruence class of the principal character
under reduction of all central-character values modulo that ideal.

Completeness supplies the principal-character index and lying over supplies
the ideal. These choices construct the data without any hypotheses about
Brauer maps or character-section identities. Exposed block definitions let
subsequent modular arguments use their congruence meaning directly.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/PrincipalBlockConstruction.lean` (revision `c3503435`).
The campaign-specific conversion to Z* input data belongs to the campaign,
so this reusable construction imports only central-character prerequisites.
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock

namespace PrincipalBlockConstruction

open BlockPreliminaries

attribute [local instance] Fintype.ofFinite

universe u

/-- The principal character as a function on conjugacy classes. -/
@[expose] def ordinaryPrincipalCharacter
    (G : Type u) [Group G] : ConjClassFunction G := 1

@[simp] theorem ordinaryPrincipalCharacter_apply
    {G : Type u} [Group G] (c : ConjClasses G) :
    ordinaryPrincipalCharacter G c = 1 := rfl

/-- The constant-one ordinary class function is irreducible. -/
theorem ordinaryPrincipalCharacter_irreducible
    {G : Type u} [Group G] [Finite G] :
    IsIrreducibleConjCharacter (ordinaryPrincipalCharacter G) := by
  let T : Representation ℂ G (Fin 1 → ℂ) :=
    Representation.trivial ℂ G (Fin 1 → ℂ)
  constructor
  · refine ⟨1, T, ?_⟩
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    change 1 = T.character g
    simp [T, Representation.character]
  · simp [classFunctionInner, ordinaryPrincipalCharacter]

/-- The completely constructed ordinary congruence-block data. -/
structure PrincipalCongruenceBlockData
    (G : Type u) [Group G] [Finite G] where
  I : Type
  fintypeI : Fintype I
  decidableEqI : DecidableEq I
  chi : I → ConjClassFunction G
  complete : IsCompleteIrreducibleCharacterFamily chi
  eta : ℂ
  eta_spec : IsPrimitiveRoot eta (Nat.card G)
  primeIdeal : Ideal (cyclotomicOrder eta)
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
@[expose] def block (d : PrincipalCongruenceBlockData G) : Finset d.I :=
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
      (2 : cyclotomicOrder d.eta) = 0 :=
  two_eq_zero_mod_liesOver d.primeIdeal d.primeIdeal_liesOverTwo

end PrincipalCongruenceBlockData

/-- The ordinary principal congruence block exists for every finite group. -/
theorem exists_principalCongruenceBlockData
    (G : Type u) [Group G] [Finite G] :
    Nonempty (PrincipalCongruenceBlockData G) := by
  classical
  rcases classFunction_span_irreducible_characters (G := G) with
    ⟨I, hI, chi, hcomplete, _hspan⟩
  let : Fintype I := hI
  let : DecidableEq I := Classical.decEq I
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

end PrincipalBlockConstruction

end ModularBlock

