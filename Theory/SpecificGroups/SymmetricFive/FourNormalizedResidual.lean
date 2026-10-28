module

public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Three-free two-perfect subgroups normalized by an alternating four-group

A two-perfect subgroup of S₅ lies in A₅, since the sign image is a two-group.
If a four-group in A₅ normalizes it, the join is still three-free. Lagrange
leaves orders four and twenty for that join. A₅ has no subgroup of order
twenty: its perfect coset action on three points is trivial. The join is
therefore a two-group, and its two-perfect subgroup is trivial.

This supplies the residual-image calculation in Aschbacher–Smith 13.6.26(2),
printed p.934, for the actual action on the A₅ quotient. Only the order-four
and normalization properties of the prescribed Sylow image are needed.
-/

public section
open Subgroup
namespace SymmetricFive
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private theorem a5_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem no_twenty (J : Subgroup A5) : Nat.card J ≠ 20 := by
  intro hc
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (⊤ : Subgroup A5) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := A5)).symm.toMonoidHom) (topEquiv (G := A5)).symm.surjective
  have hi : J.index ≤ 4 := by
    have hh := J.card_mul_index
    rw [hc, a5_card] at hh
    omega
  have hj : J = ⊤ := top_unique
    ((perfect_le_normalCore_of_index_le_four (⊤ : Subgroup A5) J hi).trans J.normalCore_le)
  rw [hj, Nat.card_congr (topEquiv (G := A5)).toEquiv, a5_card] at hc
  norm_num at hc

private theorem three_free_four (J : Subgroup S5) (hJ : J ≤ A5)
    (h4 : 4 ∣ Nat.card J) (h3 : ¬ 3 ∣ Nat.card J) : Nat.card J = 4 := by
  have hd : Nat.card J ∣ 60 := a5_card ▸ card_dvd_of_le hJ
  have hn : Nat.card J ≠ 20 := by
    have h := no_twenty (J.subgroupOf A5)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv] at h
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 60 ≠ 0)⟩
  have hdivs : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
  rw [hdivs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all

/-- A three-free two-perfect subgroup of S₅ normalized by an order-four
subgroup of A₅ is trivial. -/
theorem twoPerfect_eq_bot_of_three_free_normalized_four
    (A B : Subgroup S5) (hA : A ≤ A5) (hAc : Nat.card A = 4)
    (hn : A ≤ normalizer (B : Set S5)) (hB : IsPPerfect 2 B)
    (h3 : ¬ 3 ∣ Nat.card B) : B = ⊥ := by
  have hu : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1)
    (by simp [Nat.card_eq_fintype_card, Fintype.card_units_int])
  have hsign := hB.hom_eq_one_of_isPGroup hu (Equiv.Perm.sign.comp B.subtype)
  have hBA : B ≤ A5 := by
    intro b hb
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact DFunLike.congr_fun hsign (⟨b, hb⟩ : B)
  have hJ3 : ¬ 3 ∣ Nat.card (B ⊔ A : Subgroup S5) := by
    intro hd
    have hm := dvd_mul_of_dvd_right hd (Nat.card (B ⊓ A : Subgroup S5))
    rw [← card_mul_eq_card_inf_mul_card_sup_of_normalizes B A hn, hAc] at hm
    exact (Nat.prime_three.dvd_mul.mp hm).elim h3 (by norm_num)
  have hJ4 : 4 ∣ Nat.card (B ⊔ A : Subgroup S5) :=
    hAc ▸ card_dvd_of_le (show A ≤ B ⊔ A from le_sup_right)
  have hc : Nat.card (B ⊔ A : Subgroup S5) = 4 :=
    three_free_four (B ⊔ A) (sup_le hBA hA) hJ4 hJ3
  have htwo : IsPGroup 2 (B ⊔ A : Subgroup S5) := IsPGroup.of_card (n := 2) hc
  let f : B →* (B ⊔ A : Subgroup S5) := inclusion le_sup_left
  have hf := hB.hom_eq_one_of_isPGroup htwo f
  apply bot_unique
  intro b hb
  have he := DFunLike.congr_fun hf (⟨b, hb⟩ : B)
  exact congrArg Subtype.val he

/-- The same vanishing criterion with the original Sylow subgroup of A₅
and its literal inclusion in S₅. -/
theorem twoPerfect_eq_bot_of_three_free_normalized_sylow
    (P : Sylow 2 A5) (B : Subgroup S5)
    (hn : (P : Subgroup A5).map (alternatingGroup (Fin 5)).subtype ≤ normalizer (B : Set S5))
    (hB : IsPPerfect 2 B) (h3 : ¬ 3 ∣ Nat.card B) : B = ⊥ := by
  apply twoPerfect_eq_bot_of_three_free_normalized_four
    ((P : Subgroup A5).map (alternatingGroup (Fin 5)).subtype) B (map_subtype_le _) _ hn hB h3
  rw [card_map_of_injective Subtype.val_injective, P.card_eq_multiplicity, a5_card]
  decide +kernel
end SymmetricFive
