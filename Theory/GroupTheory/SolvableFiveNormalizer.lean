module

public import Theory.GroupTheory.Hall.Existence
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic

/-!
# Three divisors in five-normalizers of solvable groups

In a finite solvable group whose order is not divisible by 81, every Sylow
five-normalizer has order divisible by 3 whenever the group does. Indeed,
embed the Sylow five-subgroup in a Hall {3,5}-subgroup. Its index is a power
of three at most 27. Sylow counting forces the five-subgroup to be normal
in this Hall subgroup, whose order retains the factor of three.

This is the elementary Hall and Sylow reduction for the last contradiction
in Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, VI, printed p.630. The bound on the three-part is a separate,
essential input; solvability alone does not give the conclusion.

Without the three-part bound, an order-five Sylow with three-free normalizer
still produces a concrete obstruction: a nontrivial three-subgroup normalized
by the five-subgroup and having trivial five-centralizer. This follows from
the unique Sylow three-subgroup of a Hall {3,5}-subgroup.
-/

namespace Sylow

open Subgroup

/-- With three-part at most 27, a solvable group's factor of three already
occurs in each Sylow five-normalizer. -/
public theorem three_dvd_card_normalizer_of_not_eightyone_dvd
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (h81 : ¬ 81 ∣ Nat.card G) (P : Sylow 5 G) (h3 : 3 ∣ Nat.card G) :
    3 ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {p | p.val = 3 ∨ p.val = 5}
  have hPπ : IsPiSubgroup π (P : Subgroup G) := by
    intro p hp
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    exact Or.inr (Nat.prime_eq_prime_of_dvd_pow p.property (by decide) (hk ▸ hp))
  have hinv : IsInvariant Unit G (P : Subgroup G) := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨H, hHall, _, hPH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hsolv (by simp) π (P : Subgroup G) hPπ hinv
  let PH := P.subtype hPH
  have hi : ∃ n : ℕ, PH.toSubgroup.index = 3 ^ n := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := H ⧸ PH.toSubgroup)).ne' ?_⟩
    intro p hp hpi
    have hmem := hHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩
      (hpi.trans PH.toSubgroup.index_dvd_card)
    rcases hmem with h | h
    · exact h
    · have hp5 : p = 5 := h
      subst p
      exact (PH.not_dvd_index hpi).elim
  obtain ⟨n, hn⟩ := hi
  have hnlt : n < 4 := by
    by_contra h
    apply h81
    have hd : 3 ^ 4 ∣ PH.toSubgroup.index := by
      rw [hn]
      exact pow_dvd_pow 3 (by omega)
    exact (hd.trans PH.toSubgroup.index_dvd_card).trans H.card_subgroup_dvd_card
  have hcount : Nat.card (Sylow 5 H) = 1 := by
    have hd : Nat.card (Sylow 5 H) ∣ 3 ^ n := hn ▸ PH.card_dvd_index
    obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hd
    have hklt : k < 4 := lt_of_le_of_lt hkn hnlt
    have hm := card_sylow_modEq_one 5 H
    rw [hk] at hm ⊢
    interval_cases k <;> norm_num [Nat.ModEq] at *
  let _ : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hcount).1
  have hN : H ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mp PH.normal_of_subsingleton
  have h3H : 3 ∣ Nat.card H := by
    have hi3 : ¬ 3 ∣ H.index := fun h =>
      hHall.p_in_pi_of_p_dvd_index ⟨3, by decide⟩ h (Or.inl rfl)
    have hm : 3 ∣ Nat.card H * H.index := H.card_mul_index.symm ▸ h3
    exact ((show Nat.Prime 3 by decide).dvd_mul.mp hm).resolve_right hi3
  exact h3H.trans (Subgroup.card_dvd_of_le hN)

/-- If a Sylow five-subgroup has order five and a three-free normalizer,
any factor of three in a solvable group produces a nontrivial three-subgroup
normalized by the five-subgroup, with trivial five-centralizer. A Hall
{3,5}-subgroup has a unique Sylow three-subgroup: its number divides five
and is congruent to one modulo three. -/
public theorem exists_normalized_three_subgroup_of_not_three_dvd_normalizer
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (P : Sylow 5 G) (hP : Nat.card P = 5)
    (hN : ¬ 3 ∣ Nat.card (normalizer (P : Set G))) (h3 : 3 ∣ Nat.card G) :
    ∃ T : Subgroup G, IsPGroup 3 T ∧ T ≠ ⊥ ∧
      (P : Subgroup G) ≤ normalizer (T : Set G) ∧
      T ⊓ centralizer (P : Set G) = ⊥ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {p | p.val = 3 ∨ p.val = 5}
  have hPπ : IsPiSubgroup π (P : Subgroup G) := by
    intro p hp
    rw [hP] at hp
    exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hp |>.resolve_left p.property.ne_one)
  obtain ⟨H, hHall, _, hPH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hsolv (by simp) π (P : Subgroup G) hPπ ⟨fun _ _ => Iff.rfl⟩
  let PH := P.subtype hPH
  obtain ⟨n, hn⟩ : ∃ n : ℕ, PH.toSubgroup.index = 3 ^ n := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := H ⧸ PH.toSubgroup)).ne' ?_⟩
    intro p hp hpi
    have hmem := hHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩
      (hpi.trans PH.toSubgroup.index_dvd_card)
    rcases hmem with h | h
    · exact h
    · have hp5 : p = 5 := h
      subst p
      exact (PH.not_dvd_index hpi).elim
  have hPHcard : Nat.card PH = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).trans hP
  have hHcard : Nat.card H = 5 * 3 ^ n := by
    rw [← PH.toSubgroup.card_mul_index, hn, hPHcard]
  have hcount : Nat.card (Sylow 3 H) = 1 := by
    let Q : Sylow 3 H := Classical.choice inferInstance
    have hd : Nat.card (Sylow 3 H) ∣ 5 * 3 ^ n := by
      rw [← hHcard]
      exact Q.card_dvd_index.trans Q.toSubgroup.index_dvd_card
    have hc : Nat.Coprime (Nat.card (Sylow 3 H)) (3 ^ n) :=
      (show Nat.Prime 3 by decide).coprime_pow_of_not_dvd (not_dvd_card_sylow 3 H)
    have hd5 : Nat.card (Sylow 3 H) ∣ 5 := hc.dvd_of_dvd_mul_right hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd5 with he | he
    · exact he
    · have hm := card_sylow_modEq_one 3 H
      rw [he] at hm
      norm_num [Nat.ModEq] at hm
  let _ : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let Q : Sylow 3 H := Classical.choice inferInstance
  let _ : Q.toSubgroup.Normal := Q.normal_of_subsingleton
  let T := Q.toSubgroup.map H.subtype
  have hT : IsPGroup 3 T := Q.isPGroup'.map H.subtype
  have hHN : H ≤ normalizer (T : Set G) := by
    have hh := Q.toSubgroup.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] using hh
  have h3H : 3 ∣ Nat.card H := by
    have hi3 : ¬ 3 ∣ H.index := fun h =>
      hHall.p_in_pi_of_p_dvd_index ⟨3, by decide⟩ h (Or.inl rfl)
    have hm : 3 ∣ Nat.card H * H.index := H.card_mul_index.symm ▸ h3
    exact ((show Nat.Prime 3 by decide).dvd_mul.mp hm).resolve_right hi3
  have h3T : 3 ∣ Nat.card T := by
    rw [card_map_of_injective H.subtype_injective]
    exact Q.dvd_card_of_dvd_card h3H
  refine ⟨T, hT, ?_, hPH.trans hHN, ?_⟩
  · intro he
    simp [he] at h3T
  · apply Subgroup.card_eq_one.mp
    apply (hT.to_le (show T ⊓ centralizer (P : Set G) ≤ T from inf_le_left)).card_eq_or_dvd.resolve_right
    intro hd
    exact hN (hd.trans (card_dvd_of_le
      (inf_le_right.trans (centralizer_le_normalizer (P : Set G)))))

end Sylow
