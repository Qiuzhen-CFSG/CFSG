module

public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Prime rank from a centralized cyclic section

If a normal subgroup of order prime to `p` has index `p` in `L`,
and an independent elementary abelian subgroup `P` centralizes `L` modulo
that normal subgroup, the quotient contains an elementary abelian subgroup
of order `p * |P|`. Its Sylow preimage lifts isomorphically, giving the same
prime-rank lower bound in the original group.

This supplies the rank calculation in Aschbacher–Smith, Lemma 15.4.23,
printed p.1165: take `p = 3`, `|P| = 9`, and the normal layer `O₂(L)`.
-/

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- A central cyclic quotient and an independent elementary abelian subgroup
force one more unit of odd prime rank. -/
public theorem Subgroup.primeRank_ge_of_centralized_cyclic_section
    {p n : ℕ} [Fact p.Prime] (N L P : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (hindex : N.relIndex L = p)
    (hN : Nat.Coprime p (Nat.card N)) [IsElementaryAbelian p P]
    (hP : Nat.card P = p ^ n) (hdis : Disjoint L P)
    (hcomm : ⁅P, L⁆ ≤ N) : n + 1 ≤ primeRank p G := by
  let f := QuotientGroup.mk' N
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have hcop : Nat.Coprime p (Nat.card f.ker) := hker.symm ▸ hN
  have hLc : Nat.card (L.map f) = p := by
    rw [← relIndex_ker, hker, hindex]
  let : IsCyclic (L.map f) := isCyclic_of_prime_card hLc
  let : IsElementaryAbelian p (L.map f) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      rw [← hLc]
      exact pow_card_eq_one' }
  let : IsElementaryAbelian p (P.map f) := IsElementaryAbelian.map f
  have hPc : Nat.card (P.map f) = p ^ n := by
    let e := MulEquiv.ofBijective (f.subgroupMap P)
      ⟨fun x y h => injective_comp_subtype_of_coprime_ker f hcop P
        (IsElementaryAbelian.isPGroup p P) (congrArg Subtype.val h),
        f.subgroupMap_surjective P⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hP
  have hcentral : P.map f ≤ centralizer (L.map f : Set (G ⧸ N)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, hker]
    exact hcomm
  have hmapdis : Disjoint (L.map f) (P.map f) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hxL, hxP⟩
    obtain ⟨p, hp, rfl⟩ := hxP
    have hpL : p ∈ L := by
      have : p ∈ (L.map f).comap f := hxL
      rw [comap_map_eq_self (hker.le.trans hNL)] at this
      exact this
    have he : p = 1 := hdis.le_bot ⟨hpL, hp⟩
    simp [he]
  let : IsElementaryAbelian p (L.map f ⊔ P.map f : Subgroup (G ⧸ N)) :=
    IsElementaryAbelian.sup_of_le_centralizer hcentral
  have hsize : Nat.card (L.map f ⊔ P.map f : Subgroup (G ⧸ N)) = p ^ (n + 1) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hcentral.trans (centralizer_le_normalizer _)) hmapdis, hLc, hPc]
    rw [pow_succ, mul_comm]
  exact IsElementaryAbelian.primeRank_ge_of_coprime_quotient f
    (QuotientGroup.mk'_surjective N) hcop _ hsize
