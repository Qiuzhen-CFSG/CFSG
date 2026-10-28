module
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.Tactic.LinearCombination

/-!
# Sparse root identities for two natural binary factors

The off-diagonal blocks of an extension satisfy the same commuting and
root-chain relations as its actors. Two spare coordinates force products
of common-center root displacements to vanish in the dual orientation.
These are matrix identities, not an assumed splitting theorem.

Source: the higher-dimensional branch of Aschbacher–Smith B.4.9(2)(i),
printed pp.92–95; the printed proof stops at dimension five.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
open Matrix

private lemma spare {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ a : Fin n, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ a ≠ l := by
  classical
  have hc : ({i,j,k,l} : Finset (Fin n)).card < Fintype.card (Fin n) := by
    have h' : ({i,j,k,l} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i,j,k,l} : Finset (Fin n)).card < Finset.univ.card by simpa using hc)
  exact ⟨a, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha⟩

/-- The scalar commuting-root relation for the natural-by-dual bimodule. -/
def DualCommutes {n : ℕ} (c : Fin n → Fin n → Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ i j k l, i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ r s,
    (if r = i then c k l j s else 0) + (if s = k then c i j r l else 0) =
      (if r = k then c i j l s else 0) + (if s = i then c k l r j else 0)

/-- The common-center double displacement vanishes. The two spare indices
are what make this argument valid in all higher binary dimensions. -/
theorem dual_root_product_zero {n : ℕ} (hn : 5 ≤ n)
    (c : Fin n → Fin n → Matrix (Fin n) (Fin n) (ZMod 2)) (hc : DualCommutes c)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (r s : Fin n) :
    (if r = i then c i k j s else 0) + (if s = i then c i j r k else 0) = 0 := by
  obtain ⟨a, hai, haj, hak, _⟩ := spare hn i j k i
  obtain ⟨b, hbi, hbj, hbk, hba⟩ := spare hn i j k a
  by_cases hri : r = i
  · subst r
    by_cases hsi : s = i
    · subst s
      have h₁ := hc i j b k hij hbk hbj.symm hik.symm i b
      have h₂ := hc i k a j hik haj hak.symm hij.symm a i
      have h₃ := hc a j b k haj hbk hbj.symm hak.symm a b
      simp only [ite_true, if_neg hbi, if_neg hbi.symm, if_neg hai,
        if_neg hai.symm, if_neg hba, if_neg hba.symm, add_zero] at h₁ h₂ h₃ ⊢
      linear_combination h₁ - h₂ - h₃
    · obtain ⟨a, hai, haj, hak, has⟩ := spare hn i j k s
      have h₁ := hc i j i k hij hik hij.symm hik.symm i s
      have h₂ := hc i j a k hij hak haj.symm hik.symm a s
      simp only [ite_true, if_neg hsi, if_neg hai,
        if_neg has.symm, add_zero] at h₁ h₂ ⊢
      exact h₁.trans h₂.symm
  · by_cases hsi : s = i
    · subst s
      obtain ⟨a, hai, haj, hak, har⟩ := spare hn i j k r
      have h := hc i j a k hij hak haj.symm hik.symm r a
      simp only [if_neg hri, ite_true, if_neg har.symm, if_neg hai,
        add_zero, zero_add] at h ⊢
      exact h
    · simp only [if_neg hri, if_neg hsi, add_zero]

private lemma transvection_left {n : ℕ} (i j r s : Fin n)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ((1 + Matrix.single i j (1 : ZMod 2)) * M) r s = M r s + if r = i then M j s else 0 := by
  change (Matrix.transvection i j (1 : ZMod 2) * M) r s = _
  by_cases h : r = i
  · subst r
    simp
  · simp [h]

private lemma transvection_right {n : ℕ} (i j r s : Fin n)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (M * Matrix.transvection i j (1 : ZMod 2)) r s = M r s + if s = j then M r i else 0 := by
  by_cases h : s = j
  · subst s
    simp
  · simp [h]

/-- Off-diagonal blocks for an extension of the contragredient natural module
by the natural module. The right factor is the literal inverse transpose. -/
def IsDualDerivation {n : ℕ}
    (d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ g h, d (g * h) = g.val * d h + d g * (h⁻¹).val.transpose

/-- Values at elementary roots, with zero on the unused diagonal index pairs. -/
noncomputable def rootValues {n : ℕ}
    (d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2))
    (i j : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  if h : i ≠ j then d (SpecialLinearGroup.transvection h 1) else 0

private lemma dual_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ((SpecialLinearGroup.transvection h (1 : ZMod 2))⁻¹).val.transpose =
      Matrix.transvection j i 1 := by
  rw [SpecialLinearGroup.transvection_inv, CharTwo.neg_eq, SpecialLinearGroup.transvection_coe]
  simp [Matrix.transvection]

/-- The scalar relations are consequences of actual commuting actors. -/
theorem dualDerivation_commutes {n : ℕ}
    {d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hd : IsDualDerivation d) : DualCommutes (rootValues d) := by
  unfold DualCommutes rootValues
  intro i j k l hij hkl hjk hli r s
  simp only [dif_pos hij, dif_pos hkl]
  have hd' : ∀ g h, d (g * h) = g.val * d h + d g * (h⁻¹).val.transpose := hd
  have h := congrArg (fun g => d g r s)
    (Representation.OneCohomology.SLHigherNatural.transvection_commute hij hkl hjk hli
      (1 : ZMod 2) 1)
  simp only [hd', SpecialLinearGroup.transvection_coe, dual_transvection,
    Matrix.add_apply, transvection_left, transvection_right] at h
  change (if r = i then d (SpecialLinearGroup.transvection hkl 1) j s else 0) +
    (if s = k then d (SpecialLinearGroup.transvection hij 1) r l else 0) =
    (if r = k then d (SpecialLinearGroup.transvection hij 1) l s else 0) +
    (if s = i then d (SpecialLinearGroup.transvection hkl 1) r j else 0)
  linear_combination h

/-- Common-center elementary roots have zero double displacement in every
natural-by-dual matrix derivation, in all dimensions at least five. -/
theorem dualDerivation_root_product {n : ℕ} (hn : 5 ≤ n)
    {d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hd : IsDualDerivation d) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) :
    Matrix.single i j 1 * d (SpecialLinearGroup.transvection hik 1) +
      d (SpecialLinearGroup.transvection hij 1) * Matrix.single k i 1 = 0 := by
  ext r s
  have h := dual_root_product_zero hn (rootValues d) (dualDerivation_commutes hd)
    i j k hij hik r s
  simp only [rootValues, dif_pos hij, dif_pos hik] at h
  by_cases hr : r = i <;> by_cases hs : s = i
  · subst r; subst s; simpa using h
  · subst r; simpa [hs] using h
  · subst s; simpa [hr] using h
  · simp [hr, hs]

end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
