module
public import Theory.Character.ModularBlock.Congruence
public import Theory.GroupTheory.ZStar.OddCore
public import Theory.GroupTheory.Involution.Basic

/-!
# The principal two-block data used by the Z-star proof

This package records a complete finite family of ordinary irreducible
characters, its principal character, and a block containing that character.
Its two substantive fields are the involution-centralizer section identity
and weak orthogonality of every involution against the identity. These are
the exact modular inputs used by the ordinary-character contradiction.

The definition is separated from the induction theorem consuming it, so the
modular factory can build the package without depending on that theorem.
No block-theoretic assertion is postulated: later production modules must
construct all fields. The principal character is the shared modular
declaration, and the involution and odd core are the existing production
definitions.

Ported unchanged mathematically from the structure in
`Submission/ZStar/PrincipalBlock.lean` at historical commit `c3503435`.
-/

public section
noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar
open BenderSuzuki.PFAppendixIII
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
  chi : I → ConjClassFunction G
  complete : IsCompleteIrreducibleCharacterFamily chi
  block : Finset I
  principal : I
  principal_mem : principal ∈ block
  principal_eq : chi principal = ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter G
  section_invariance : ∀ i ∈ block, ∀ z : G, IsInvolution z → ∀ v : G,
    v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype →
    chi i (ConjClasses.mk (z * v)) = chi i (ConjClasses.mk z)
  orthogonal_one : ∀ s : G, IsInvolution s →
    ∑ i ∈ block,
      chi i (ConjClasses.mk s) * chi i (ConjClasses.mk (1 : G)) = 0


end Glauberman.ZStar

