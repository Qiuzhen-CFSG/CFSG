module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition.Cubic

/-!
# The two-core of the three-pair stabilizer in S₇

The eight products of the disjoint pair swaps form a normal two-subgroup
of the partition stabilizer. Its whole two-core lies in the standard Sylow;
conjugating by a cycle of the three pairs eliminates the eight remaining
Sylow elements. Thus this eight-group is the intrinsic embedded two-core,
and every relatively normal subgroup of order eight is equal to it.

Source: Aschbacher–Smith, proof of Lemma 14.4.11, printed p.1011
(combined manuscript of 1 March 2004).
-/

@[expose] public section
open Equiv Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry

def baseWord (i : Fin 8) : S7 :=
  (swap 0 1) ^ (i.val % 2) * (swap 2 3) ^ ((i.val / 2) % 2) *
    (swap 4 5) ^ (i.val / 4)

def B8 : Subgroup S7 where
  carrier := {g | ∃ i, baseWord i = g}
  one_mem' := ⟨0, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (show ∀ i j : Fin 8, ∃ k : Fin 8, baseWord k = baseWord i * baseWord j by decide +kernel) i j
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact (show ∀ i : Fin 8, ∃ j : Fin 8, baseWord j = (baseWord i)⁻¹ by decide +kernel) i
instance (g : S7) : Decidable (g ∈ B8) :=
  inferInstanceAs (Decidable (∃ i, baseWord i = g))

theorem B8_eq_closure : B8 = closure ({swap 0 1, swap 2 3, swap 4 5} : Set S7) := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with h | h | h <;> subst g <;> change _ ∈ B8 <;> decide

theorem B8_card : Nat.card B8 = 8 := by
  let e : Fin 8 ≃ B8 := Equiv.ofBijective (fun i => ⟨baseWord i, i, rfl⟩)
    ⟨fun i j h => (show Function.Injective baseWord by decide +kernel) (congrArg Subtype.val h),
      by rintro ⟨g, i, rfl⟩; exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr e).symm.trans (Nat.card_fin _)

theorem B8_le_standardTwo : B8 ≤ standardTwo := by
  rintro g ⟨i, rfl⟩
  exact (show ∀ i : Fin 8, baseWord i ∈ standardTwo by decide +kernel) i

theorem syntheme_normalizes_B8 : synthemeOvergroup ≤ normalizer (B8 : Set S7) := by
  apply le_normalizer_iff.mpr
  intro g hg
  have hs (a b : Fin 7) (hab : ({a,b} : Finset (Fin 7)) ∈
      ({{0,1},{2,3},{4,5}} : Finset (Finset (Fin 7)))) : g * swap a b * g⁻¹ ∈ B8 := by
    have h := Finset.mem_image_of_mem (fun t : Finset (Fin 7) => t.image g) hab
    have hp := hg.2
    change ({{0,1},{2,3},{4,5}} : Finset (Finset (Fin 7))).image (fun t => t.image g) = _ at hp
    rw [hp] at h
    simp only [Finset.image_insert, Finset.image_singleton] at h
    have ht : ∀ a b : Fin 7, ({a,b} : Finset (Fin 7)) ∈
      ({{0,1},{2,3},{4,5}} : Finset (Finset (Fin 7))) → swap a b ∈ B8 := by decide +kernel
    have he : g * swap a b * g⁻¹ = swap (g a) (g b) := by
      exact (Equiv.swap_apply_apply g a b).symm
    rw [he]
    exact ht _ _ h
  have hmap : B8 ≤ B8.comap (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [B8_eq_closure]
    rw [closure_le]
    intro x hx
    rcases hx with h | h | h <;> subst x
    · exact hs 0 1 (by decide)
    · exact hs 2 3 (by decide)
    · exact hs 4 5 (by decide)
  exact hmap

private theorem core_normalizes : synthemeOvergroup ≤ normalizer (synthemeOvergroup.pCoreIn 2 : Set S7) := by
  have h := le_normalizer_map (H := pCore 2 synthemeOvergroup) synthemeOvergroup.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h


private theorem core_le_standardTwo : synthemeOvergroup.pCoreIn 2 ≤ standardTwo := by
  have hn : standardTwo ≤ normalizer (synthemeOvergroup.pCoreIn 2 : Set S7) :=
    inf_le_right.trans core_normalizes
  have hp := (isPGroup_pCoreIn 2 synthemeOvergroup).to_sup_of_normal_left'
    standardSylow.isPGroup' hn
  exact le_sup_left.trans (standardSylow.is_maximal' hp le_sup_right).le

def pairCycle : S7 := swap 0 2 * swap 1 3 * (swap 2 4 * swap 3 5)


theorem syntheme_twoCore : synthemeOvergroup.pCoreIn 2 = B8 := by
  apply le_antisymm
  · intro g hg
    have hb := core_le_standardTwo hg
    have hr : pairCycle ∈ synthemeOvergroup := by decide
    have hc := core_le_standardTwo (le_normalizer_iff.mp core_normalizes pairCycle hr g hg)
    obtain ⟨i, hi⟩ := sylowEquiv.surjective ⟨g,hb⟩
    have he := congrArg Subtype.val hi
    change sylowWord i = g at he
    rw [← he] at hc ⊢
    exact (show ∀ i : Fin 16, pairCycle * sylowWord i * pairCycle⁻¹ ∈ standardTwo →
      sylowWord i ∈ B8 by decide +kernel) i hc
  · exact le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 3) B8_card)
      (B8_le_standardTwo.trans inf_le_right) syntheme_normalizes_B8

theorem normal_eight_eq_B8 (N : Subgroup S7) (hNP : N ≤ synthemeOvergroup)
    (hn : synthemeOvergroup ≤ normalizer (N : Set S7)) (hc : Nat.card N = 8) : N = B8 := by
  apply eq_of_le_of_card_ge
  · rw [← syntheme_twoCore]
    exact le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 3) hc) hNP hn
  · rw [B8_card, hc]



end Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry
