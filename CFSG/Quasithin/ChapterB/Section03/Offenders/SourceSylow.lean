module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd

/-!
# A simultaneous Sylow choice in odd degree

The disjoint pair swaps and the interchange of the first two pairs generate a
Sylow subgroup in degrees five and seven. Its eight or sixteen explicit words
form a group and are distinct, as certified by kernel reduction. Identifying
this group with `D ⊔ A₀` supplies the simultaneous containment required by the
source, including the exceptional group even in case (a).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2, printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders.Odd

private def optionalPair (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : i < n / 2 then pairSwap n ⟨i, h⟩ else 1

private def sourceWord (n : ℕ) (hn : n = 5 ∨ n = 7)
    (i : Fin (2 ^ (n / 2 + 1))) : Equiv.Perm (Fin n) :=
  (if i.val % 2 = 0 then 1 else optionalPair n 0) *
  (if i.val / 2 % 2 = 0 then 1 else optionalPair n 1) *
  (if i.val / 4 % 2 = 0 then 1 else optionalPair n 2) *
  (if i.val / (2 ^ (n / 2)) % 2 = 0 then 1 else kleinSecond n (by rcases hn with rfl | rfl <;> decide))

private def sourceTable (n : ℕ) (hn : n = 5 ∨ n = 7) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := Set.range (sourceWord n hn)
  one_mem' := ⟨⟨0, Nat.two_pow_pos _⟩, by rcases hn with rfl | rfl <;> rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, sourceWord n hn i * sourceWord n hn j = sourceWord n hn k := by
      rcases hn with rfl | rfl <;> decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have h : ∀ i, ∃ j, (sourceWord n hn i)⁻¹ = sourceWord n hn j := by
      rcases hn with rfl | rfl <;> decide +kernel
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, hj.symm⟩

private theorem sourceTable_eq {n : ℕ} (hn : n = 5 ∨ n = 7) :
    sourceTable n hn = D n ⊔ exceptional n (by rcases hn with rfl | rfl <;> decide) := by
  have hp (j : ℕ) : optionalPair n j ∈ D n := by
    unfold optionalPair
    split_ifs with h
    · exact pairSwap_mem ⟨j, h⟩ h
    · exact Subgroup.one_mem _
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    have hb : kleinSecond n (by rcases hn with rfl | rfl <;> decide) ∈
        exceptional n (by rcases hn with rfl | rfl <;> decide) :=
      Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))
    unfold sourceWord
    repeat' apply Subgroup.mul_mem
    all_goals split_ifs
    all_goals first | exact Subgroup.one_mem _ | exact Subgroup.mem_sup_left (hp _) |
      exact Subgroup.mem_sup_right hb
  · have hp : ∀ i : Fin (n / 2), pairSwap n i ∈ sourceTable n hn := by
      change ∀ i, ∃ j, sourceWord n hn j = pairSwap n i
      rcases hn with rfl | rfl <;> decide +kernel
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro g ⟨i, _, rfl⟩
      exact hp i
    · apply (Subgroup.closure_le _).mpr
      rintro g ((rfl | hg) | ⟨i, _, rfl⟩)
      · change ∃ j, sourceWord n hn j = _
        rcases hn with rfl | rfl <;> decide +kernel
      · rw [Set.mem_singleton_iff] at hg
        subst g
        change ∃ j, sourceWord n hn j = _
        rcases hn with rfl | rfl <;> decide +kernel
      · exact hp i

private theorem card_sourceTable {n : ℕ} (hn : n = 5 ∨ n = 7) :
    Nat.card (sourceTable n hn) = 2 ^ (n / 2 + 1) := by
  have hi : Function.Injective (sourceWord n hn) := by
    rcases hn with rfl | rfl <;> decide +kernel
  change Nat.card (Set.range (sourceWord n hn)) = _
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

/-- The source's simultaneous Sylow choice in odd degree contains `D` and `A₀`. -/
theorem exists_sylow_containing_D_exceptional {n : ℕ} (hn : n = 5 ∨ n = 7) :
    ∃ T : Sylow 2 (Equiv.Perm (Fin n)),
      (T : Subgroup (Equiv.Perm (Fin n))) =
        D n ⊔ exceptional n (by rcases hn with rfl | rfl <;> decide) := by
  let T : Sylow 2 (Equiv.Perm (Fin n)) :=
    (IsPGroup.of_card (card_sourceTable hn)).toSylow (by
      have hc := (sourceTable n hn).card_mul_index
      rw [card_sourceTable hn, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
      rcases hn with rfl | rfl <;> norm_num [Nat.factorial] at hc <;> omega)
  exact ⟨T, sourceTable_eq hn⟩

end CFSG.Quasithin.ChapterB.Offenders.Odd
