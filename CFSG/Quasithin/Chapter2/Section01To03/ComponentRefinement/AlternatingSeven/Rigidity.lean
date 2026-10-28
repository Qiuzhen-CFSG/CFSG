module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.Basic
public import CFSG.Quasithin.Chapter1.Section01
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Characteristic-two overgroups of the alternating partition stabilizer

The even stabilizer of the partition `{01,23,45,6}` contains a Sylow
2-subgroup `P` of A₇ and cyclically permutes the three nonidentity elements
of the four-group `V` of even pair flips. If a characteristic-two subgroup
`N` contains this stabilizer, its nontrivial two-core lies in `P`. Conjugation
by the three-cycle on the pairs forces that core to be exactly `V`.
The orbits of `V` are precisely the partition blocks, so its normalizer is
contained in the partition stabilizer. Thus `N` is that stabilizer.

All finite calculations concern the displayed four- and eight-element
subgroups. Ordinary maximality in S₇ is neither asserted nor used.
This supplies the missing local restriction in the proof of
Aschbacher–Smith 2.3.9(7)(c), printed p.526.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven
open Subgroup Equiv

private def a : A7 := ⟨swap 0 1 * swap 2 3, by change Perm.sign _ = 1; decide⟩
private def b : A7 := ⟨swap 0 1 * swap 4 5, by change Perm.sign _ = 1; decide⟩
private def r : A7 := ⟨swap 0 2 * swap 1 3, by change Perm.sign _ = 1; decide⟩
private def k : A7 := ⟨(swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5), by change Perm.sign _ = 1; decide⟩
private def fourEntry : Fin 4 → A7 := ![1, a, b, a*b]
private def eightEntry : Fin 8 → A7 := ![1, a, b, a*b, r, a*r, b*r, a*b*r]

private def pairFour : Subgroup A7 where
  carrier := Set.range fourEntry
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    change ∃ l, fourEntry l = fourEntry i * fourEntry j
    fin_cases i <;> fin_cases j <;> decide
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    change ∃ j, fourEntry j = (fourEntry i)⁻¹
    fin_cases i <;> decide

private def pairEight : Subgroup A7 where
  carrier := Set.range eightEntry
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    change ∃ l, eightEntry l = eightEntry i * eightEntry j
    fin_cases i <;> fin_cases j <;> decide
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    change ∃ j, eightEntry j = (eightEntry i)⁻¹
    fin_cases i <;> decide

private theorem pairEight_card : Nat.card pairEight = 8 := by
  let f : Fin 8 → pairEight := fun i => ⟨eightEntry i, ⟨i, rfl⟩⟩
  have hi : Function.Injective f := by
    intro i j he
    have hv := congrArg (fun x : pairEight => (x : A7)) he
    have hc : ∀ i j, eightEntry i = eightEntry j → i = j := by decide
    exact hc i j hv
  have hs : Function.Surjective f := by
    rintro ⟨x, i, rfl⟩
    exact ⟨i, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (by simp)

private theorem pairEight_le_stabilizer : pairEight ≤ alternatingStabilizer := by
  rintro x ⟨i, rfl⟩
  rw [mem_alternatingStabilizer]
  fin_cases i <;> decide

private theorem k_mem_stabilizer : k ∈ alternatingStabilizer := by
  rw [mem_alternatingStabilizer]
  decide

private theorem pairFour_le_pairEight : pairFour ≤ pairEight := by
  rintro x ⟨i, rfl⟩
  change ∃ j, eightEntry j = fourEntry i
  fin_cases i <;> decide

private theorem normal_subgroup_eq_pairFour {Q : Subgroup A7}
    (hQ : Q ≤ pairEight) (hne : Q ≠ ⊥)
    (hk : k ∈ normalizer (Q : Set A7)) : Q = pairFour := by
  have hconj : ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun x hx => (hk x).mp hx
  have hQfour : Q ≤ pairFour := by
    intro x hx
    obtain ⟨i, rfl⟩ := hQ hx
    have hc := hQ (hconj _ hx)
    have hcalc : ∀ i : Fin 8, (∃ j, eightEntry j = k * eightEntry i * k⁻¹) →
        ∃ j, fourEntry j = eightEntry i := by decide
    exact hcalc i hc
  apply le_antisymm hQfour
  have hex : ∃ x ∈ Q, x ≠ 1 := by
    by_contra! hn
    exact hne (le_bot_iff.mp (fun x hx => hn x hx))
  obtain ⟨x, hx, hx1⟩ := hex
  obtain ⟨i, rfl⟩ := hQfour hx
  rintro y ⟨j, rfl⟩
  have hcalc : ∀ i j : Fin 4, fourEntry i ≠ 1 →
      fourEntry j = 1 ∨ fourEntry j = fourEntry i ∨
      fourEntry j = k * fourEntry i * k⁻¹ ∨
      fourEntry j = k * (k * fourEntry i * k⁻¹) * k⁻¹ := by decide
  rcases hcalc i j hx1 with he | he | he | he
  · exact he ▸ Q.one_mem
  · exact he ▸ hx
  · exact he ▸ hconj _ hx
  · exact he ▸ hconj _ (hconj _ hx)

private theorem pairFour_orbit (i j : Fin 7) :
    i.val / 2 = j.val / 2 ↔ ∃ n : Fin 4, (fourEntry n : S7) i = j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem normalizer_pairFour_le_stabilizer :
    normalizer (pairFour : Set A7) ≤ alternatingStabilizer := by
  intro g hg
  have hf : ∀ g : A7, g ∈ normalizer (pairFour : Set A7) →
      ∀ i j : Fin 7, i.val / 2 = j.val / 2 →
        ((g : S7) i).val / 2 = ((g : S7) j).val / 2 := by
    intro g hg i j hij
    obtain ⟨n, hn⟩ := (pairFour_orbit i j).mp hij
    have hc : g * fourEntry n * g⁻¹ ∈ pairFour := (hg _).mp ⟨n, rfl⟩
    obtain ⟨l, hl⟩ := hc
    apply (pairFour_orbit _ _).mpr
    refine ⟨l, ?_⟩
    rw [hl]
    change (g : S7) ((fourEntry n : S7) ((g : S7)⁻¹ ((g : S7) i))) = (g : S7) j
    rw [Perm.inv_def, Equiv.symm_apply_apply, hn]
  change ∀ i j : Fin 7, ((g : S7) i).val / 2 = ((g : S7) j).val / 2 ↔ _
  intro i j
  refine ⟨fun h => ?_, hf g hg i j⟩
  simpa only [coe_inv, Perm.inv_def, Equiv.symm_apply_apply] using hf g⁻¹ ((normalizer _).inv_mem hg) _ _ h

private theorem pairEight_sylow_card :
    Nat.card pairEight = 2 ^ (Nat.card A7).factorization 2 := by
  rw [pairEight_card, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [Nat.factorization_def _ Nat.prime_two]
  have hzero : padicValNat 2 315 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by decide)))
  rw [show 2520 = 2 ^ 3 * 315 by decide,
    padicValNat_base_pow_mul (by decide) (by decide) 3, hzero]
  decide

/-- No proper overgroup of the partition stabilizer in A₇ has characteristic two. -/
theorem characteristicTwo_overgroup_eq (N : Subgroup A7)
    (hN : N ∈ Chapter1.He A7) (hKN : alternatingStabilizer ≤ N) :
    N = alternatingStabilizer := by
  let P : Sylow 2 A7 := Sylow.ofCard pairEight pairEight_sylow_card
  have hPN : (P : Subgroup A7) ≤ N := pairEight_le_stabilizer.trans hKN
  let T : Sylow 2 N := P.subtype hPN
  let Q : Subgroup A7 := N.pCoreIn 2
  have hQeight : Q ≤ pairEight := by
    have hQ := pCoreIn_le_sylow N T
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hQ hx
    exact hy
  have hnorm : N ≤ normalizer (Q : Set A7) := by
    rw [le_normalizer_iff]
    rintro g hg x ⟨y, hy, rfl⟩
    exact mem_map.mpr ⟨(⟨g,hg⟩ : N) * y * (⟨g,hg⟩ : N)⁻¹,
      (inferInstance : (pCore 2 N).Normal).conj_mem y hy ⟨g,hg⟩, rfl⟩
  have hQne : Q ≠ ⊥ := by
    intro he
    have ha : a ∈ Q := by
      apply hN
      refine ⟨hKN (pairEight_le_stabilizer (pairFour_le_pairEight ⟨1,rfl⟩)), ?_⟩
      rw [show N.pCoreIn 2 = ⊥ from he]
      simp [mem_centralizer_iff]
    rw [he, mem_bot] at ha
    exact (by decide : a ≠ 1) ha
  have he : Q = pairFour := normal_subgroup_eq_pairFour hQeight hQne
    (hnorm (hKN k_mem_stabilizer))
  exact le_antisymm (by rw [he] at hnorm; exact hnorm.trans normalizer_pairFour_le_stabilizer) hKN

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven
end
