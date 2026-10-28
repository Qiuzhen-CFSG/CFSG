module

public import Theory.GroupTheory.Fitting.Centralizer
public import Mathlib.GroupTheory.Sylow

/-!
# Solvable overgroups from prime-subgroup normalizers

Let S be an abelian Sylow p-subgroup of a finite group. Suppose every other
prime divides the ambient order at most once, and the normalizer of each
subgroup of that prime order has order not divisible by |S|. Then every
solvable overgroup of S normalizes S.

A nontrivial q-core of the overgroup would have order q. Its normality
would place S in the ambient normalizer, contradicting the local bound.
Thus the Fitting subgroup is the p-core. The abelian Sylow subgroup
centralizes this core, so Fitting self-centralization makes S the core.
All normality used here is relative to the solvable overgroup.

This criterion isolates the finite-group argument used for J₁ in
Aschbacher–Smith, *The Classification of Quasithin Groups*, printed p.510;
the required concrete normalizer bounds are the entries of GLS3 Table 5.3f.
-/

open Subgroup

private theorem core_eq_bot_of_prime_normalizers
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) (H : Subgroup G)
    (hSH : S ≤ H) {q : ℕ} [Fact q.Prime]
    (hsq : ¬ q ^ 2 ∣ Nat.card G)
    (hnorm : ∀ A : Subgroup G, Nat.card A = q →
      ¬ Nat.card S ∣ Nat.card (normalizer (A : Set G))) : pCore q H = ⊥ := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q) (G := H)).exists_card_eq
  have hd : q ^ n ∣ Nat.card G := by
    rw [← hn]
    exact dvd_trans (pCore q H).card_subgroup_dvd_card H.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact hsq ((pow_dvd_pow q hh).trans hd)
  by_cases hz : n = 0
  · apply Subgroup.card_eq_one.mp
    simpa only [hz, pow_zero] using hn
  have hn1 : n = 1 := by omega
  have hc : Nat.card (pCore q H) = q := by simpa only [hn1, pow_one] using hn
  let A := (pCore q H).map H.subtype
  have hA : Nat.card A = q := by
    rw [card_map_of_injective H.subtype_injective]
    exact hc
  have hHN : H ≤ normalizer (A : Set G) := by
    have hh := (pCore q H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] using hh
  exact (hnorm A hA (card_dvd_of_le (hSH.trans hHN))).elim

/-- Prime-normalizer bounds force an abelian Sylow subgroup to be normal
in every solvable overgroup. -/
public theorem solvable_overgroup_le_normalizer_of_prime_normalizers
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [IsMulCommutative S]
    (hsq : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 2 ∣ Nat.card G)
    (hnorm : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : Subgroup G, Nat.card A = q →
      ¬ Nat.card S ∣ Nat.card (normalizer (A : Set G)))
    (H : Subgroup G) [Group.IsSolvable H] (hSH : (S : Subgroup G) ≤ H) :
    H ≤ normalizer (S : Set G) := by
  let T : Sylow p H := S.subtype hSH
  let _ : IsMulCommutative T := by
    change IsMulCommutative ((S : Subgroup G).subgroupOf H)
    infer_instance
  have hf : fittingSubgroup H = pCore p H := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      have hq := Nat.prime_of_mem_primeFactors q.val.property
      by_cases he : q.val.val = p
      · rw [he]
      · let _ : Fact q.val.val.Prime := ⟨hq⟩
        rw [core_eq_bot_of_prime_normalizers (S : Subgroup G) H hSH
          (hsq _ hq he) (hnorm _ hq he)]
        exact bot_le
    · exact pCore_le_fitting H p
  have hFT : fittingSubgroup H ≤ (T : Subgroup H) :=
    hf ▸ fitting_pCore_le_sylow T
  have hTF : (T : Subgroup H) ≤ fittingSubgroup H := by
    apply le_trans ?_ (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance)
    apply le_trans ?_ (centralizer_le hFT)
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have he : (S : Subgroup G).subgroupOf H = fittingSubgroup H := le_antisymm hTF hFT
  apply (normal_subgroupOf_iff_le_normalizer hSH).mp
  rw [he]
  infer_instance
