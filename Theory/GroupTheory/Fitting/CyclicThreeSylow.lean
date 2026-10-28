module
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.PResidual.CyclicThree

/-!
# Sylow order with cyclic three-core

A two-subgroup acts faithfully on any self-centralizing normal three-group.
When that group is cyclic, its automorphism order has two-part at most two,
so the two-subgroup has order at most two. In a solvable two-reduced group
whose prime cores above three vanish, the Fitting subgroup is the three-core.
Fitting self-centralization therefore supplies the same bound if that core
is cyclic.

Source application: the solvable-local reductions in Aschbacher–Smith,
14.7.27–29, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
namespace Theory.GroupTheory
open Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- A two-subgroup acting on a self-centralizing cyclic three-group has order at most two. -/
theorem two_subgroup_card_le_two_of_cyclic_three
    (N : Subgroup D) [N.Normal] [IsCyclic N] (hN : IsPGroup 3 N)
    (hC : centralizer (N : Set D) ≤ N) (A : Subgroup D) (hA : IsPGroup 2 A) :
    Nat.card A ≤ 2 := by
  let f : A →* MulAut N := (MulAut.conjNormal : D →* MulAut N).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : (a : D) ∈ centralizer (N : Set D) := by
      intro n hn
      have he := congrArg (fun e : MulAut N => (e ⟨n,hn⟩ : D)) ha
      change (a : D) * n * (a : D)⁻¹ = n at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hd : Disjoint A N := hA.disjoint_of_coprime hN (by decide)
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨a.property,hC hc⟩))
  have hd : Nat.card A ∣ Nat.card (MulAut N) := card_dvd_of_injective f hf
  rw [IsCyclic.card_mulAut] at hd
  obtain ⟨n,hn⟩ := hN.exists_card_eq
  rw [hn] at hd
  cases n with
  | zero =>
    have h1 : Nat.card A ∣ 1 := by simpa using hd
    exact (Nat.le_of_dvd (by decide : 0 < 1) h1).trans (by decide)
  | succ n =>
    rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)] at hd
    obtain ⟨k,hk⟩ := hA.exists_card_eq
    have hc : Nat.Coprime (Nat.card A) (3 ^ n) := by
      rw [hk]
      exact ((by decide : Nat.Coprime 2 3).pow_left k).pow_right n
    exact Nat.le_of_dvd (by decide : 0 < 2) (hc.dvd_of_dvd_mul_left hd)

/-- The cyclic three-core case of the solvable, two-reduced Fitting reduction. -/
theorem sylow_card_le_two_of_solvable_cyclic_threeCore
    (hs : Group.IsSolvable D) (h2 : pCore 2 D = ⊥)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p D = ⊥)
    [IsCyclic (pCore 3 D)] (S : Sylow 2 D) : Nat.card S ≤ 2 := by
  have hF : fittingSubgroup D = pCore 3 D := by
    apply le_antisymm _ (pCore_le_fitting D 3)
    rw [fitting_eq_sup_pCore]
    apply iSup_le
    intro p
    have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.property
    by_cases hp2 : p.1.1 = 2
    · rw [hp2,h2]; exact bot_le
    by_cases hp3 : p.1.1 = 3
    · rw [hp3]
    rw [hlarge p.1.1 hp (by have := hp.two_le; omega)]
    exact bot_le
  have hc : centralizer (pCore 3 D : Set D) ≤ pCore 3 D := by
    rw [←hF]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  exact two_subgroup_card_le_two_of_cyclic_three (pCore 3 D) pCore_isPGroup
    hc (S : Subgroup D) S.isPGroup'

end Theory.GroupTheory
