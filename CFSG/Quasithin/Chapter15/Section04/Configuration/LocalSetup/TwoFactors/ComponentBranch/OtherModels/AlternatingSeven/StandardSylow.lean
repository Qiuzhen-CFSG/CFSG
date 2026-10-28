module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# The standard Sylow two-subgroup for the A₇ fixed-action obstruction

The permutations `(2 3 4 5)(0 1)` and `(3 5)(0 1)` generate a dihedral
subgroup of order eight, hence a Sylow two-subgroup of A₇. Its centralizer
in S₇ consists of the identity, the square of the rotation, `(0 1)`, and
their product. The finite permutation identities are checked by the kernel.

This is the permutation calculation used to exclude the A₇ components in
Aschbacher–Smith F.6.18(7),(9) in the proof of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
abbrev K := alternatingGroup (Fin 7)
def r : K := ⟨swap 2 3 * swap 3 4 * swap 4 5 * swap 0 1, by
  simp [mem_alternatingGroup, Perm.sign_mul]⟩
def s : K := ⟨swap 3 5 * swap 0 1, by simp [mem_alternatingGroup, Perm.sign_mul]⟩
def t : Perm (Fin 7) := swap 0 1

def sylowElements : Finset K := {1, r, r^2, r^3, s, r*s, r^2*s, r^3*s}
def sylowSubgroup : Subgroup K where
  carrier := (sylowElements : Set K)
  one_mem' := by simp [sylowElements]
  mul_mem' := by
    intro x y hx hy
    change x ∈ sylowElements at hx
    change y ∈ sylowElements at hy
    simp only [sylowElements, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  inv_mem' := by
    intro x hx
    change x ∈ sylowElements at hx
    simp only [sylowElements, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma sylowSubgroup_card : Nat.card sylowSubgroup = 8 := by
  change Nat.card (sylowElements : Set K) = 8
  let _ := Fintype.ofFinset sylowElements (fun _ => Iff.rfl)
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset sylowElements (fun _ => Iff.rfl)]
  decide +kernel

lemma card_K : Nat.card K = 2520 := by
  change Nat.card (alternatingGroup (Fin 7)) = 2520
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

noncomputable def standardSylow : Sylow 2 K :=
  Sylow.ofCard sylowSubgroup (by
    rw [sylowSubgroup_card, card_K, show 2520 = 2^3 * (3^2 * 5 * 7) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)])

@[simp] theorem standardSylow_coe : (standardSylow : Subgroup K) = sylowSubgroup := rfl

theorem r_mem_standardSylow : r ∈ (standardSylow : Subgroup K) := by
  change r ∈ sylowElements
  simp [sylowElements]

theorem s_mem_standardSylow : s ∈ (standardSylow : Subgroup K) := by
  change s ∈ sylowElements
  simp [sylowElements]

def centralizerElements : Finset (Perm (Fin 7)) :=
  {1, (r : Perm (Fin 7))^2, t, (r : Perm (Fin 7))^2 * t}

theorem centralizerElements_card : Nat.card (centralizerElements : Set (Perm (Fin 7))) = 4 := by
  let _ := Fintype.ofFinset centralizerElements (fun _ => Iff.rfl)
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset centralizerElements (fun _ => Iff.rfl)]
  decide +kernel

theorem t_mem_centralizerElements : t ∈ centralizerElements := by simp [centralizerElements]

theorem t_ne_one : t ≠ 1 := by decide

theorem centralizer_calculation (g : Perm (Fin 7))
    (hr : g * (r : Perm (Fin 7)) = (r : Perm (Fin 7)) * g)
    (hs : g * (s : Perm (Fin 7)) = (s : Perm (Fin 7)) * g) :
    g = 1 ∨ g = (r : Perm (Fin 7))^2 ∨ g = t ∨ g = (r : Perm (Fin 7))^2 * t := by
  have hr0 := congrArg (fun f : Perm (Fin 7) => f 0) hr
  have hr2 := congrArg (fun f : Perm (Fin 7) => f 2) hr
  have hr3 := congrArg (fun f : Perm (Fin 7) => f 3) hr
  have hr4 := congrArg (fun f : Perm (Fin 7) => f 4) hr
  have hr6 := congrArg (fun f : Perm (Fin 7) => f 6) hr
  have hs0 := congrArg (fun f : Perm (Fin 7) => f 0) hs
  have hs2 := congrArg (fun f : Perm (Fin 7) => f 2) hs
  change g 1 = (r : Perm (Fin 7)) (g 0) at hr0
  change g 3 = (r : Perm (Fin 7)) (g 2) at hr2
  change g 4 = (r : Perm (Fin 7)) (g 3) at hr3
  change g 5 = (r : Perm (Fin 7)) (g 4) at hr4
  change g 6 = (r : Perm (Fin 7)) (g 6) at hr6
  change g 1 = (s : Perm (Fin 7)) (g 0) at hs0
  change g 2 = (s : Perm (Fin 7)) (g 2) at hs2
  have h6 : g 6 = 6 :=
    (show ∀ i : Fin 7, i = (r : Perm (Fin 7)) i → i = 6 by decide +kernel) _ hr6
  have h0 : g 0 = 0 ∨ g 0 = 1 := by
    have hc := (show ∀ i : Fin 7, (r : Perm (Fin 7)) i = (s : Perm (Fin 7)) i →
      i = 0 ∨ i = 1 ∨ i = 6 by decide +kernel) _ (hr0.symm.trans hs0)
    rcases hc with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := g.injective (h.trans h6.symm)
      contradiction
  have h2 : g 2 = 2 ∨ g 2 = 4 := by
    have hc := (show ∀ i : Fin 7, i = (s : Perm (Fin 7)) i →
      i = 2 ∨ i = 4 ∨ i = 6 by decide +kernel) _ hs2
    rcases hc with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := g.injective (h.trans h6.symm)
      contradiction
  clear hr hs hr6 hs0 hs2
  rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
  · left
    ext i
    fin_cases i <;> simp_all [r, Perm.mul_apply, Equiv.swap_apply_def]
  · right; left
    ext i
    fin_cases i <;> simp_all [r, Perm.mul_apply, pow_two, Equiv.swap_apply_def]
  · right; right; left
    ext i
    fin_cases i <;> simp_all [r, t, Perm.mul_apply, Equiv.swap_apply_def]
  · right; right; right
    ext i
    fin_cases i <;> simp_all [r, t, Perm.mul_apply, pow_two, Equiv.swap_apply_def]
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
