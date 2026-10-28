module

public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# Cubic fixed spaces in the five-point natural module

An order-three permutation of five points is a three-cycle. Conjugacy reduces
the fixed-space calculation to one cycle, whose fixed full permutation module
has dimension three. Removing the constant summand leaves two dimensions in
the natural module. Only the representative's 32 binary words are enumerated.

Source: Aschbacher--Smith, H.15.4, printed p.400, and B.3.1.
-/

public section

open scoped BigOperators
open Representation.BinaryOffender
namespace BinaryPermutation.PointedSix

private def threeCycle : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 0 2

private lemma threeCycle_isThreeCycle : threeCycle.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma orderThree_isConj (g : Equiv.Perm (Fin 5)) (hg : orderOf g = 3) :
    IsConj threeCycle g := by
  have hcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by
      have h := Finset.card_le_univ g.support
      simp only [Fintype.card_fin] at h
      rw [hg]
      omega)
  have hs : g.support.card = 3 := hcycle.orderOf.symm.trans hg
  exact Equiv.Perm.isConj_of_cycleType_eq
    (threeCycle_isThreeCycle.cycleType.trans
      ((card_support_eq_three_iff.mp hs).cycleType.symm))

private noncomputable def fullFixedEquiv (g : Equiv.Perm (Fin 5)) :
    fixedSpace (representation (Fin 5)) (Subgroup.zpowers g) ≃
      {v : Fin 5 → ZMod 2 // ∀ i, v (g i) = v i} where
  toFun v := ⟨v.val, fun i => by
    have h := (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    simpa using (congrFun h (g i)).symm⟩
  invFun v := ⟨v.val, (mem_fixedSpace_zpowers_iff _ _ _).mpr (by
    ext i
    simpa using (v.property (g.symm i)).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma threeCycle_fixed_card :
    Fintype.card {v : Fin 5 → ZMod 2 // ∀ i, v (threeCycle i) = v i} = 8 := by
  decide +kernel

private lemma threeCycle_full_fixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 5))
      (Subgroup.zpowers threeCycle)) = 3 := by
  have he := Nat.card_congr (fullFixedEquiv threeCycle)
  rw [Nat.card_eq_fintype_card (α := {v : Fin 5 → ZMod 2 // ∀ i, v (threeCycle i) = v i}),
    threeCycle_fixed_card] at he
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (representation (Fin 5)) (Subgroup.zpowers threeCycle))
  rw [he, Nat.card_eq_fintype_card, ZMod.card] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm

lemma natural_fixed_finrank_of_order_three (g : Equiv.Perm (Fin 5))
    (hg : orderOf g = 3) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 5))
      (Subgroup.zpowers g)) = 2 := by
  obtain ⟨t,ht⟩ := isConj_iff.mp (orderThree_isConj g hg)
  have hc := fixedCodim_map_conj (representation (Fin 5)) (Subgroup.zpowers threeCycle) t
  rw [MonoidHom.map_zpowers] at hc
  change fixedCodim (representation (Fin 5)) (Subgroup.zpowers (t * threeCycle * t⁻¹)) = _ at hc
  rw [ht] at hc
  have hseed := fixedCodim_add_finrank (representation (Fin 5)) (Subgroup.zpowers threeCycle)
  rw [threeCycle_full_fixed_finrank, finrank_full, Fintype.card_fin] at hseed
  have h := fixedCodim_add_finrank (naturalRepresentation (Fin 5)) (Subgroup.zpowers g)
  rw [fixedCodim_natural_eq_full_odd (Fin 5) (by decide), hc,
    finrank_natural_odd (Fin 5) (by decide), Fintype.card_fin] at h
  omega
end BinaryPermutation.PointedSix
