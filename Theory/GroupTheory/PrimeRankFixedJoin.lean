module

public import Theory.PrimeRank
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Elementary abelian fixed subgroups and prime-rank obstructions

An elementary abelian subgroup of order `p^n` centralized by an independent
actor of order `p` generates with the actor an elementary abelian subgroup
of order `p^(n+1)`. The cardinality bounds the generator rank, and hence the
ambient prime rank. This is the elementary final step of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Corollary A.2.6, p. 34.

The rank lower bound uses Mathlib's exponent bound on the order of a finitely
generated abelian group; the join calculation uses the disjoint product formula.
-/

open scoped IsMulCommutative
open Subgroup

private theorem rank_le_card (A : Type*) [Group A] [Finite A] : Group.rank A ≤ Nat.card A := by
  classical
  let := Fintype.ofFinite A
  simpa using Group.rank_le (S := Finset.univ) (by simp)

/-- Every abelian p-subgroup contributes its generator rank to the prime rank. -/
public theorem Subgroup.rank_le_primeRank_of_abelian_pGroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) (A : Subgroup G)
    (hAp : IsPGroup p A) (hAc : IsMulCommutative A) : Group.rank A ≤ primeRank p G := by
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro n ⟨B, _, _, hfg, hn⟩
    exact hn.trans ((rank_le_card B).trans
      (Nat.card_le_card_of_injective B.subtype Subtype.val_injective))
  · exact ⟨A, hAp, hAc, inferInstance, le_rfl⟩

/-- The order of an elementary abelian group bounds its generator rank below. -/
public theorem IsElementaryAbelian.rank_ge_of_card
    {A : Type*} [Group A] [Finite A] {p n : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] (hcard : Nat.card A = p ^ n) : n ≤ Group.rank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hd := card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A))
  rw [hcard] at hd
  exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd

/-- A prime-order element outside a subgroup generates a disjoint subgroup. -/
public theorem Subgroup.disjoint_zpowers_of_prime_order_not_mem
    {G : Type*} [Group G] (E : Subgroup G) {p : ℕ} [Fact p.Prime]
    (x : G) (hx : orderOf x = p) (hxE : x ∉ E) : Disjoint E (zpowers x) := by
  have hc : Nat.card (zpowers x) = p := (Nat.card_zpowers x).trans hx
  let : Fact (Nat.card (zpowers x)).Prime := ⟨hc ▸ Fact.out⟩
  rcases (E.subgroupOf (zpowers x)).eq_bot_or_eq_top_of_prime_card with h | h
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro a ha
    have hh : (⟨a, ha.2⟩ : zpowers x) ∈ E.subgroupOf (zpowers x) := ha.1
    rw [h] at hh
    exact congrArg Subtype.val (mem_bot.mp hh)
  · exfalso
    apply hxE
    have hh : (⟨x, mem_zpowers x⟩ : zpowers x) ∈ E.subgroupOf (zpowers x) := by rw [h]; trivial
    exact hh

/-- An independent centralizing actor adds a factor of p to the elementary subgroup. -/
public theorem IsElementaryAbelian.fixed_join_card
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (E : Subgroup G) [IsElementaryAbelian p E] (x : G)
    (hx : orderOf x = p) (hdis : Disjoint E (zpowers x))
    (hfix : E ≤ centralizer ({x} : Set G)) (hcard : Nat.card E = p ^ n) :
    IsElementaryAbelian p (E ⊔ zpowers x : Subgroup G) ∧
      Nat.card (E ⊔ zpowers x : Subgroup G) = p ^ (n + 1) := by
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hc : zpowers x ≤ centralizer (E : Set G) := by
    apply zpowers_le.mpr
    intro e he
    exact mem_centralizer_singleton_iff.mp (hfix he)
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hc, ?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint E (zpowers x)
    (hc.trans (centralizer_le_normalizer _)) hdis, hcard, Nat.card_zpowers, hx, pow_succ]

/-- A concrete elementary abelian subgroup gives an ambient prime-rank lower bound. -/
public theorem IsElementaryAbelian.primeRank_ge_of_card
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (E : Subgroup G) [IsElementaryAbelian p E] (hcard : Nat.card E = p ^ n) :
    n ≤ primeRank p G :=
  (IsElementaryAbelian.rank_ge_of_card hcard).trans
    (E.rank_le_primeRank_of_abelian_pGroup p
      (IsElementaryAbelian.isPGroup p E) inferInstance)

/-- A fixed elementary abelian subgroup and an outer prime-order actor force
one more unit of prime rank in the ambient group. -/
public theorem IsElementaryAbelian.primeRank_ge_of_fixed_join
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (E : Subgroup G) [IsElementaryAbelian p E] (x : G)
    (hx : orderOf x = p) (hxE : x ∉ E)
    (hfix : E ≤ centralizer ({x} : Set G)) (hcard : Nat.card E = p ^ n) :
    n + 1 ≤ primeRank p G := by
  obtain ⟨hjoin, hsize⟩ := IsElementaryAbelian.fixed_join_card E x hx
    (E.disjoint_zpowers_of_prime_order_not_mem x hx hxE) hfix hcard
  let := hjoin
  exact IsElementaryAbelian.primeRank_ge_of_card (E ⊔ zpowers x) hsize

/-- A centerless subgroup containing a full-rank elementary abelian p-subgroup
has p-prime centralizer in an ambient group of the same p-rank bound. -/
public theorem Subgroup.prime_not_dvd_card_centralizer_of_full_rank
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (L E : Subgroup G) [IsElementaryAbelian p E] (hEL : E ≤ L)
    (hcard : Nat.card E = p ^ n) (hrank : primeRank p G ≤ n)
    (hZ : center L = ⊥) : ¬ p ∣ Nat.card (centralizer (L : Set G)) := by
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  have hxG : orderOf (x : G) = p :=
    (orderOf_injective (centralizer (L : Set G)).subtype Subtype.val_injective x).trans hx
  have hxL : (x : G) ∉ L := by
    intro hmem
    have hz : (⟨x, hmem⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext ((mem_centralizer_iff.mp x.property) l l.property)
    rw [hZ] at hz
    have he : (x : G) = 1 := congrArg Subtype.val (mem_bot.mp hz)
    have hone : orderOf (x : G) = 1 := he ▸ orderOf_one
    have := (Fact.out : p.Prime).one_lt
    omega
  have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp x.property) a (hEL ha))
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hxG
    (fun hm => hxL (hEL hm)) hfix hcard
  omega

/-- A p-element inducing an automorphism of order p has order p when the
kernel of the action has order prime to p. -/
public theorem MonoidHom.orderOf_eq_prime_of_primePower_of_kernel
    {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hk : ¬ p ∣ Nat.card f.ker) (x : G)
    (hxp : ∃ n, x ^ (p ^ n) = 1) (hx : orderOf (f x) = p) : orderOf x = p := by
  have hxpow : f (x ^ p) = 1 := by rw [map_pow, ← hx, pow_orderOf_eq_one]
  let y : f.ker := ⟨x ^ p, hxpow⟩
  have hyo : orderOf y ∣ Nat.card f.ker := orderOf_dvd_natCard y
  obtain ⟨n, hn⟩ := hxp
  have hyp : y ^ (p ^ n) = 1 := by
    apply Subtype.ext
    change (x ^ p) ^ (p ^ n) = 1
    rw [← pow_mul, Nat.mul_comm p, pow_mul, hn, one_pow]
  have hdiv : orderOf y ∣ p ^ n := orderOf_dvd_of_pow_eq_one hyp
  have hc : Nat.Coprime (Nat.card f.ker) (p ^ n) :=
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hk).symm.pow_right n
  have hy : y = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc hyo hdiv)
  have hp : x ^ p = 1 := congrArg Subtype.val hy
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hp) (hx ▸ orderOf_map_dvd f x)

/-- An elementary subgroup in a quotient with p-prime kernel gives the same
prime-rank lower bound in the original group. -/
public theorem IsElementaryAbelian.primeRank_ge_of_coprime_quotient
    {G H : Type*} [Group G] [Finite G] [Group H] {p n : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime p (Nat.card f.ker))
    (E : Subgroup H) [IsElementaryAbelian p E] (hcard : Nat.card E = p ^ n) :
    n ≤ primeRank p G := by
  obtain ⟨A, hA, _, hsize⟩ :=
    Subgroup.exists_elementaryAbelian_map_eq_of_surjective_coprime f hf hk E
  let := hA
  exact IsElementaryAbelian.primeRank_ge_of_card A (hsize.trans hcard)
