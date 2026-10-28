module
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic
/-!
# Cubic centralizers on six letters

Both possible cubic cycle types have centralizer of order eighteen.
Consequently a faithful two-group centralizing a cubic permutation has
order at most two. The order formula avoids a census of permutation pairs.

Source application: the marked factor-normalizer step in Aschbacher--Smith
14.3.22, printed p.999.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix
/-- A cubic permutation on six letters has centralizer of order eighteen. -/
theorem cubic_centralizer_card (a : Equiv.Perm (Fin 6)) (ha : orderOf a=3) :
    Nat.card (centralizer ({a}:Set (Equiv.Perm (Fin 6))))=18 := by
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order (ha ▸ Nat.prime_three)
  have hb := Equiv.Perm.sum_cycleType_le a
  rw [hn,ha,Multiset.sum_replicate] at hb
  norm_num [nsmul_eq_mul] at hb
  have hnle : n≤1 := by omega
  interval_cases n <;> rw [Equiv.Perm.nat_card_centralizer,hn,ha] <;> norm_num

/-- A faithful two-group of six-letter permutations centralizing a cubic
has order at most two. -/
theorem twoGroup_card_le_two_of_centralizes_cubic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : P →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a=3)
    (hcomm : ∀ x : P, Commute (f x) a) : Nat.card P≤2 := by
  let j : P →* centralizer ({a}:Set (Equiv.Perm (Fin 6))) :=
    f.codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr (hcomm x).eq)
  have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
  have hd := card_dvd_of_injective j hj
  rw [cubic_centralizer_card a ha] at hd
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  rw [hn] at hd ⊢
  have hnle := (Nat.prime_two.pow_dvd_iff_le_factorization (by decide : 18≠0)).mp hd
  have hfac : Nat.factorization 18 2=1 := by
    rw [show 18=2*3^2 by decide, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow]
    simp [Nat.prime_two.factorization,Nat.prime_three.factorization]
  rw [hfac] at hnle
  exact (Nat.pow_le_pow_right (by decide : 0<2) hnle).trans_eq (by decide)
end Theory.SpecificGroups.SymmetricSix
