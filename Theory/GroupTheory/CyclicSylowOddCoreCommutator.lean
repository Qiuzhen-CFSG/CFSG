module

public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.PGroupCore

/-!
# Commutators with a prime odd core

In a finite group with trivial two-core and cyclic Sylow two-subgroup,
every nontrivial subgroup of that Sylow moves the whole odd core when the
odd core has prime order. Burnside transfer supplies the odd complement.
If the commutator vanished, both the complement and the abelian Sylow
would centralize the actor, making it a normal two-subgroup. Primality
then turns nontrivial displacement into the whole odd core.

This supplies the cyclic-model calculation in Aschbacher--Smith 15.2.13(2),
printed pp.1111--1112 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial subgroup of a cyclic Sylow moves the prime odd core of a
group with trivial two-core. -/
theorem oddCore_commutator_eq_of_cyclic_sylow
    (P : Sylow 2 G) (hP : IsCyclic P) (heven : 2 ∣ Nat.card G)
    (hcore : pCore 2 G = ⊥) (hprime : (Nat.card (pPrimeCore 2 G)).Prime)
    (B : Subgroup G) (hBP : B ≤ P) (hB : B ≠ ⊥) :
    pPrimeCore 2 G = ⁅pPrimeCore 2 G,B⁆ := by
  let O := pPrimeCore 2 G
  have hgen := (P.isComplement'_pPrimeCore_of_isCyclic hP heven).sup_eq_top
  have hle : ⁅O,B⁆ ≤ O := commutator_le_left O B
  have hne : ⁅O,B⁆ ≠ ⊥ := by
    intro he
    have hOC : O ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.mp he
    let := hP
    have hPC : (P : Subgroup G) ≤ centralizer (B : Set G) := by
      intro p hp b hb
      exact congrArg Subtype.val (mul_comm (⟨b,hBP hb⟩ : P) ⟨p,hp⟩)
    have hNC : normalizer (B : Set G) = ⊤ := by
      apply top_unique
      rw [←hgen]
      exact (sup_le hPC hOC).trans (centralizer_le_normalizer _)
    let : B.Normal := normalizer_eq_top_iff.mp hNC
    have hbcore : B ≤ pCore 2 G := le_sSup ⟨inferInstance,P.isPGroup'.to_le hBP⟩
    exact hB (bot_unique (hcore ▸ hbcore))
  have hdiv := card_dvd_of_le hle
  rcases (Nat.dvd_prime hprime).mp hdiv with hc | hc
  · exact (hne (eq_bot_of_card_eq _ hc)).elim
  · exact (eq_of_le_of_card_ge hle hc.ge).symm

end Theory.GroupTheory
