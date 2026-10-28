module

public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The three-prime core of the small permutation models

The symmetric group on three letters has no normal two-subgroup, and its
order leaves no other possible nontrivial three-prime core. In degree five
a nontrivial normal subgroup contains A₅, whose order is divisible by three.
Simplicity gives the same argument for A₆. These are the permutation models
in Aschbacher–Smith B.5.6(2)–(4), printed p.105.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups

theorem symmetricThree_threePrimeCore : pPrimeCore 3 (Equiv.Perm (Fin 3)) = ⊥ := by
  have h₂ : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have h := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using h.symm
  apply pPrimeCore_eq_bot_of_card_dvd (p := 3) (q := 2) 1 1 _ h₂
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem symmetricFive_threePrimeCore : pPrimeCore 3 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp)
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hn)
  have hcop := (pPrimeCore_coprime_card (p := 3) (G := Equiv.Perm (Fin 5))).of_dvd_right
    (Subgroup.card_dvd_of_le hle)
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [hc] at hcop
  norm_num at hcop

theorem alternatingSix_threePrimeCore : pPrimeCore 3 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pPrimeCore 3 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top
    with hb | ht
  · exact hb
  · have hcop := pPrimeCore_coprime_card (p := 3) (G := alternatingGroup (Fin 6))
    rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] at hcop
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num
    rw [hc] at hcop
    norm_num at hcop

theorem cyclicThree_threePrimeCore : pPrimeCore 3 (Multiplicative (ZMod 3)) = ⊥ := by
  have hp : IsPGroup 3 (Multiplicative (ZMod 3)) := IsPGroup.of_card (n := 1)
    (by simp [Nat.card_eq_fintype_card])
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    (hp.orderOf_coprime (pPrimeCore_coprime_card (p := 3) (G := Multiplicative (ZMod 3))) x)
    dvd_rfl ((pPrimeCore 3 (Multiplicative (ZMod 3))).orderOf_dvd_natCard hx)

end Theory.SpecificGroups
