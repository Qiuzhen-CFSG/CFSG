module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Burnside
public import Theory.GroupTheory.ConjugacyClassSize
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvability from an abelian subgroup of prime-power index

Intersecting with a normal subgroup and mapping to the quotient preserve
abelianness and prime-power index. Induction on the group order reduces to
a simple group. If the abelian subgroup is trivial, the group is a p-group.
Otherwise one of its nonidentity elements has p-power conjugacy-class size,
and Burnside's argument forces the simple group to be abelian.

The scalar subgroup in `TwoGroupExclusion` is the concrete consumer: if the
two-point stabilizer is a two-group, its index is a power of two.

Source: GLS, Volume 4, Chapter 1, Lemma 3.8(b),
`refs/KGroup/GLS4/Chapter1.tex`, lines 419–430. The proof also works without
the source's coprimality condition on the subgroup order.
-/

open Subgroup
open scoped IsMulCommutative

private theorem subgroupOf_index_dvd_of_normal
    {G : Type*} [Group G] [Finite G] (K N : Subgroup G) [N.Normal] :
    (K.subgroupOf N).index ∣ K.index := by
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes N K
    (show K ≤ normalizer (N : Set G) by simp [Subgroup.normalizer_eq_top])
  have hN := relIndex_mul_relIndex (⊥ : Subgroup G) (N ⊓ K) N bot_le inf_le_left
  have hK := relIndex_mul_relIndex (⊥ : Subgroup G) K (N ⊔ K) bot_le le_sup_right
  simp only [relIndex_bot_left, inf_relIndex_left] at hN hK
  have he : K.relIndex N = K.relIndex (N ⊔ K) := by
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.card (N ⊓ K : Subgroup G) * Nat.card K from
        Nat.mul_pos Nat.card_pos Nat.card_pos)
    calc
      Nat.card (N ⊓ K : Subgroup G) * Nat.card K * K.relIndex N =
          Nat.card N * Nat.card K := by rw [← hN]; ring
      _ = Nat.card (N ⊓ K : Subgroup G) * Nat.card (N ⊔ K : Subgroup G) := hprod
      _ = Nat.card (N ⊓ K : Subgroup G) * Nat.card K * K.relIndex (N ⊔ K) := by
        rw [← hK, mul_assoc]
  change K.relIndex N ∣ K.index
  rw [he]
  exact relIndex_dvd_index_of_le le_sup_right

/-- A finite group with an abelian subgroup of prime-power index is solvable.
In particular this applies to an abelian Hall 2' subgroup. -/
public theorem Subgroup.isSolvable_of_isMulCommutative_of_prime_power_index
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [IsMulCommutative K]
    {p n : ℕ} (hp : p.Prime) (hindex : K.index = p ^ n) : Group.IsSolvable G := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G n with
  | h m ih =>
    let : Fact p.Prime := ⟨hp⟩
    by_cases hsub : Subsingleton G
    · let := hsub
      exact Group.isSolvable_of_comm (fun x y => Subsingleton.elim _ _)
    let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    by_cases hsimp : IsSimpleGroup G
    · let := hsimp
      by_cases hK : K = ⊥
      · have hcard : Nat.card G = p ^ n := by simpa [hK] using hindex
        exact @IsNilpotent.to_isSolvable G _ ((IsPGroup.of_card hcard).isNilpotent)
      · obtain ⟨x, hxK, hxne⟩ := K.bot_or_exists_ne_one.resolve_left hK
        have hKC : K ≤ centralizer ({x} : Set G) := by
          intro y hy
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hxK)
        have hc : Nat.card (ConjClasses.mk x).carrier ∣ p ^ n := by
          rw [ConjClasses.nat_card_carrier_eq_index_centralizer, ← hindex]
          exact index_dvd_of_le hKC
        obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hc
        have hcomm := IsSimpleGroup.isMulCommutative_of_prime_power_conjClass x hxne hp hk
        exact Group.isSolvable_of_comm hcomm.is_comm.comm
    · have hex : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
        by_contra h
        apply hsimp
        refine ⟨fun N hN => ?_⟩
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (by_contra fun ht => h ⟨N, hN, hb, ht⟩)
      obtain ⟨N, hN, hbot, htop⟩ := hex
      let := hN
      have hcard : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := N.card_mul_index
      have hNpos : 0 < Nat.card N := Nat.card_pos
      have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hNbig : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot
      have hQbig : 1 < Nat.card (G ⧸ N) := N.one_lt_index_of_ne_top htop
      have hNlt : Nat.card N < m := by nlinarith
      have hQlt : Nat.card (G ⧸ N) < m := by nlinarith
      apply (Group.isSolvable_iff_subgroup_quotient N).mpr
      constructor
      · have hd : (K.subgroupOf N).index ∣ p ^ n :=
          hindex ▸ subgroupOf_index_dvd_of_normal K N
        obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
        exact ih _ hNlt (K.subgroupOf N) hk rfl
      · let q := QuotientGroup.mk' N
        have hd : (K.map q).index ∣ p ^ n := hindex ▸ K.index_map_dvd
          (QuotientGroup.mk'_surjective N)
        obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
        exact ih _ hQlt (K.map q) hk rfl

