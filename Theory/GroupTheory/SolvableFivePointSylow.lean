module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.PPrimeCore
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

/-!
# Sylow two-subgroups of solvable five-point permutation groups

A solvable subgroup of `S₅` with trivial two-core has cyclic Sylow
 two-subgroups of order at most four.

The Fitting subgroup lies in the odd core, so its order divides fifteen.
Its nilpotence and squarefree order make it cyclic. A kernel-checked
five-point permutation certificate excludes order fifteen. When the Fitting
subgroup has order three or five, self-centralization makes the conjugation
action of each Sylow two-subgroup faithful. The cyclic automorphism group
then supplies both conclusions. Trivial Fitting subgroup means trivial group.

This is the finite solvable permutation calculation used in Janko–Thompson,
Math. Z. 113 (1970), printed p.389.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem fifteen_power_certificate : ∀ g : Equiv.Perm (Fin 5),
    g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

private theorem fitting_card (K : Subgroup (Equiv.Perm (Fin 5))) (hcore : pCore 2 K = ⊥) :
    Nat.card (fittingSubgroup K) = 1 ∨ Nat.card (fittingSubgroup K) = 3 ∨
      Nat.card (fittingSubgroup K) = 5 := by
  let F := fittingSubgroup K
  have hle : F ≤ pPrimeCore 2 K := by
    dsimp [F]
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq : q.val.val = 2
    · rw [hq, hcore]
      exact bot_le
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := K)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors q.val.property)).mpr (Ne.symm hq)).pow_right _
  have hodd : Nat.Coprime 2 (Nat.card F) :=
    pPrimeCore_coprime_card.of_dvd_right (Subgroup.card_dvd_of_le hle)
  have hd : Nat.card F ∣ 120 := by
    have hh := F.card_subgroup_dvd_card.trans K.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh ⊢
    exact hh
  have hd15 : Nat.card F ∣ 15 := by
    have hcop : (Nat.card F).Coprime 8 := by
      simpa using hodd.symm.pow_right 3
    exact hcop.dvd_of_dvd_mul_left hd
  have hsq15 : Squarefree (15 : ℕ) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hd
    have hh := Nat.le_of_dvd (by decide : 0 < 15) hd
    have : p ≤ 3 := by nlinarith
    interval_cases p <;> norm_num at *
  have hsq : Squarefree (Nat.card F) := hsq15.squarefree_of_dvd hd15
  let _ : IsZGroup F := IsZGroup.of_squarefree hsq
  let _ : IsCyclic F := inferInstance
  have hcases : Nat.card F = 1 ∨ Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 15 := by
    have arith : ∀ n : ℕ, n ∣ 15 → n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
      intro n hn
      have hh := Nat.le_of_dvd (by decide : 0 < 15) hn
      interval_cases n <;> norm_num at *
    exact arith _ hd15
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F)
    have hg15 : orderOf g = 15 := hg.trans h
    have hperm : orderOf ((g : K) : Equiv.Perm (Fin 5)) = 15 := by
      simpa only [Subgroup.orderOf_coe] using hg15
    have hpow : (((g : K) : Equiv.Perm (Fin 5))) ^ 15 = 1 := by
      rw [← hperm]
      exact pow_orderOf_eq_one _
    rcases fifteen_power_certificate g hpow with h3 | h5
    · have hh := orderOf_dvd_of_pow_eq_one h3
      rw [hperm] at hh
      norm_num at hh
    · have hh := orderOf_dvd_of_pow_eq_one h5
      rw [hperm] at hh
      norm_num at hh

private theorem prime_fitting_sylow
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    (hp : Nat.Coprime 2 p) (hF : Nat.card (fittingSubgroup G) = p)
    (R : Sylow 2 G) : IsCyclic R ∧ Nat.card R ≤ p - 1 := by
  let F := fittingSubgroup G
  let _ : IsCyclic F := isCyclic_of_prime_card hF
  let eAut : MulAut F ≃* (ZMod p)ˣ := by
    have h := IsCyclic.mulAutMulEquiv F
    rw [hF] at h
    exact h
  let _ : IsCyclic (MulAut F) := isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let action : R →* MulAut F := MulAut.conjNormal.comp (R : Subgroup G).subtype
  have hdisj : Disjoint (R : Subgroup G) F := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
    rw [hn, hF]
    exact hp.pow_left n
  have hinj : Function.Injective action := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply hdisj.le_bot
    refine ⟨x.property, centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv ?_⟩
    intro f hf
    have he := congrArg (fun a : MulAut F => (a ⟨f, hf⟩ : G))
      (show MulAut.conjNormal (x : G) = (1 : MulAut F) from hx)
    change (x : G) * f * (x : G)⁻¹ = f at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  refine ⟨isCyclic_of_injective action hinj, ?_⟩
  have hcard : Nat.card (MulAut F) = p - 1 := by
    rw [IsCyclic.card_mulAut, hF, Nat.totient_prime Fact.out]
  exact hcard ▸ Nat.card_le_card_of_injective action hinj

/-- Every Sylow two-subgroup of a solvable subgroup of `S₅` with trivial
 two-core is cyclic and has order at most four. -/
public theorem Sylow.isCyclic_and_card_le_four_of_solvable_five_point
    (K : Subgroup (Equiv.Perm (Fin 5)))
    (hsolv : Group.IsSolvable K) (hcore : pCore 2 K = ⊥)
    (R : Sylow 2 K) : IsCyclic R ∧ Nat.card R ≤ 4 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases fitting_card K hcore with h1 | h3 | h5
  · let _ : Group.IsSolvable K := hsolv
    have hK : Nat.card K = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp
        ((Subgroup.eq_bot_iff_card _).mpr h1)
    let _ : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hK).1
    exact ⟨inferInstance, (by
      have hh := (R : Subgroup K).card_le_card_group
      rw [hK] at hh
      exact hh.trans (by decide))⟩
  · have h := prime_fitting_sylow hsolv (by decide : Nat.Coprime 2 3) h3 R
    exact ⟨h.1, h.2.trans (by decide)⟩
  · exact prime_fitting_sylow hsolv (by decide : Nat.Coprime 2 5) h5 R
