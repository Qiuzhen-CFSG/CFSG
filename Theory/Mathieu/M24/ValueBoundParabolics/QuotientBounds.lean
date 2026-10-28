module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Local invariants of symmetric-three quotients

A group isomorphic to S₃ has generalized Fitting subgroup of order three
and two-rank at most one. The proof kills the component layer by solvability,
identifies the Fitting subgroup with the normal Sylow three-subgroup, and
uses the cyclic Sylow two-subgroup for the rank bound. All cores are intrinsic.

These are the local calculations for the generating families in
Aschbacher–Smith, E.4.3, printed pp. 241–242 (PDF pp. 252–253).
-/

public section
open Subgroup
namespace Theory.GroupTheory
private theorem s3_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
private theorem s3_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

variable {Q : Type*} [Group Q] [Finite Q]

/-- The local generalized-Fitting and rank conditions supplied by an actual S₃ equivalence. -/
theorem symmetricThree_generalizedFitting_card_and_primeRank (e : Q ≃* (Equiv.Perm (Fin 3))) :
    Nat.card (generalizedFitting Q) = 3 ∧ primeRank 2 Q ≤ 1 := by
  have hcard : Nat.card Q = 6 := (Nat.card_congr e.toEquiv).trans s3_card
  have hk : pCore 2 Q = ⊥ := by
    have h := ker_eq_twoCore_of_surjective_perm_three e.toMonoidHom e.surjective (by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      exact IsPGroup.of_subsingleton 2 _)
    rw [← h]
    exact e.toMonoidHom.ker_eq_bot e.injective
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := s3_solvable
  let : Group.IsSolvable Q := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomp : componentLayer Q = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    rintro C ⟨_, hC⟩
    let : IsQuasisimple C := hC
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  have hf : fittingSubgroup Q = pCore 3 Q := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      have hp := Nat.prime_of_mem_primeFactors p.val.property
      have hd := Nat.dvd_of_mem_primeFactors p.val.property
      have hd6 : p.val.val ∣ 6 := hcard ▸ hd
      have he : p.val.val = 2 ∨ p.val.val = 3 := by
        have := hp.dvd_mul.mp (show p.val.val ∣ 2 * 3 from hd6)
        rcases this with h | h
        · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
        · exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h |>.resolve_left hp.ne_one)
      rcases he with he | he
      · rw [he, hk]
        exact bot_le
      · rw [he]
    · exact pCore_le_fitting Q 3
  have hc : Nat.card (pCore 3 Q) = 3 := by
    let P : Sylow 3 Q := Classical.choice inferInstance
    have hP : Nat.card (P : Subgroup Q) = 3 := by
      rw [P.card_eq_multiplicity, hcard]
      decide +kernel
    have hi : (P : Subgroup Q).index = 2 := by
      have := (P : Subgroup Q).index_mul_card
      rw [hP, hcard] at this
      omega
    have hn : (P : Subgroup Q).Normal := normal_of_index_eq_two hi
    have he : pCore 3 Q = (P : Subgroup Q) :=
      le_antisymm (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨hn, P.isPGroup'⟩)
    rwa [he]
  constructor
  · simpa only [generalizedFitting, hcomp, sup_bot_eq, hf] using hc
  · let P : Sylow 2 Q := Classical.choice inferInstance
    apply P.primeRank_le_one_of_isCyclic
    apply isCyclic_of_prime_card (p := 2)
    rw [P.card_eq_multiplicity, hcard]
    decide +kernel
end Theory.GroupTheory
