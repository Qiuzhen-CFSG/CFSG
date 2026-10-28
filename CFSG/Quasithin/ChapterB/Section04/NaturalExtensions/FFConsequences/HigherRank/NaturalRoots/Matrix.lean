module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.RootRelations
import Mathlib.Tactic.LinearCombination

/-!
# Common-axis root products for two natural binary factors

The off-diagonal block of an ordinary linear extension section is a matrix
bimodule derivation. Root squares kill the unwanted row and column entries;
commuting roots kill the other off-diagonal entries. A root chain through a
spare coordinate kills diagonal entries outside the root support, and a
three-index chain gives the remaining corner identity. Thus common-column
root displacements have zero product, uniformly in the dimension.

This is the natural-orientation matrix calculation for the higher-dimensional
branch of Aschbacher–Smith B.4.9(2)(i), printed pp.92–95. The printed FF proof
stops at dimension five. The actual extension and original-actor applications
are in the parent `NaturalRoots` module; no FF or splitting premise is used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix
open Representation.OneCohomology.SLHigherNatural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank

/-- The off-diagonal block law when both factors are the column natural action. -/
def IsNaturalDerivation {n : ℕ}
    (d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ g h, d (g * h) = g.val * d h + d g * h.val

variable {n : ℕ}
  {d : SpecialLinearGroup (Fin n) (ZMod 2) → Matrix (Fin n) (Fin n) (ZMod 2)}

private lemma left_root (i j r s : Fin n) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ((1 + Matrix.single i j (1 : ZMod 2)) * M) r s = M r s + if r = i then M j s else 0 := by
  change (Matrix.transvection i j (1 : ZMod 2) * M) r s = _
  by_cases h : r = i
  · subst r; simp
  · simp [h]

private lemma right_root (i j r s : Fin n) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (M * (1 + Matrix.single i j (1 : ZMod 2))) r s = M r s + if s = j then M r i else 0 := by
  change (M * Matrix.transvection i j (1 : ZMod 2)) r s = _
  by_cases h : s = j
  · subst s; simp
  · simp [h]

private lemma at_one (hd : IsNaturalDerivation d) : d 1 = 0 := by
  have h := hd 1 1
  simp only [mul_one, SpecialLinearGroup.coe_one, one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero (d 1)).symm)

private lemma square (hd : IsNaturalDerivation d) {i j : Fin n} (hij : i ≠ j)
    (r s : Fin n) :
    (if r = i then d (SpecialLinearGroup.transvection hij 1) j s else 0) +
      (if s = j then d (SpecialLinearGroup.transvection hij 1) r i else 0) = 0 := by
  have ht : SpecialLinearGroup.transvection hij (1 : ZMod 2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
    simpa only [CharTwo.neg_eq] using SpecialLinearGroup.transvection_mul_neg hij (1 : ZMod 2)
  have h := congrArg (fun M => M r s) (hd (SpecialLinearGroup.transvection hij 1)
    (SpecialLinearGroup.transvection hij 1))
  rw [ht, at_one hd] at h
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.zero_apply,
    left_root, right_root] at h
  linear_combination (norm := (ring_nf; simp only [CharTwo.two_eq_zero]; ring)) -h

private lemma commutes (hd : IsNaturalDerivation d) {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (r s : Fin n) :
    (if r = i then d (SpecialLinearGroup.transvection hkl 1) j s else 0) +
      (if s = l then d (SpecialLinearGroup.transvection hij 1) r k else 0) =
    (if r = k then d (SpecialLinearGroup.transvection hij 1) l s else 0) +
      (if s = j then d (SpecialLinearGroup.transvection hkl 1) r i else 0) := by
  have hd' := hd
  change ∀ g h, d (g * h) = g.val * d h + d g * h.val at hd'
  have h := congrArg (fun g => d g r s) (transvection_commute hij hkl hjk hli
    (1 : ZMod 2) 1)
  simp only [hd', SpecialLinearGroup.transvection_coe, Matrix.add_apply, left_root, right_root] at h
  linear_combination h

private lemma chain (hd : IsNaturalDerivation d) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (1 + Matrix.single i j (1 : ZMod 2)) * d (SpecialLinearGroup.transvection hjk 1) +
      d (SpecialLinearGroup.transvection hij 1) * (1 + Matrix.single j k (1 : ZMod 2)) =
    (1 + Matrix.single j k (1 : ZMod 2)) *
      ((1 + Matrix.single i k (1 : ZMod 2)) * d (SpecialLinearGroup.transvection hij 1)) +
      ((1 + Matrix.single j k (1 : ZMod 2)) * d (SpecialLinearGroup.transvection hik 1) +
        d (SpecialLinearGroup.transvection hjk 1) * (1 + Matrix.single i k (1 : ZMod 2))) *
          (1 + Matrix.single i j (1 : ZMod 2)) := by
  have hd' := hd
  change ∀ g h, d (g * h) = g.val * d h + d g * h.val at hd'
  have h := congrArg d (transvection_chain hij hjk hik (1 : ZMod 2) 1)
  simpa only [one_mul, hd', SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_assoc] using h

private lemma root_row (hd : IsNaturalDerivation d) {i j s : Fin n}
    (hij : i ≠ j) (hsj : s ≠ j) :
    d (SpecialLinearGroup.transvection hij 1) j s = 0 := by
  simpa only [ite_true, if_neg hsj, add_zero] using square hd hij i s

private lemma root_column (hd : IsNaturalDerivation d) {i j r : Fin n}
    (hij : i ≠ j) (hri : r ≠ i) :
    d (SpecialLinearGroup.transvection hij 1) r i = 0 := by
  simpa only [if_neg hri, ite_true, zero_add] using square hd hij r j

private lemma spare (hn : 4 ≤ n) (i j r : Fin n) :
    ∃ a : Fin n, a ≠ i ∧ a ≠ j ∧ a ≠ r := by
  classical
  have hc : ({i,j,r} : Finset (Fin n)).card < Fintype.card (Fin n) := by
    have h' : ({i,j,r} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i,j,r} : Finset (Fin n)).card < Finset.univ.card by simpa using hc)
  exact ⟨a, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha⟩

-- A chain through a coordinate outside the root and the tested diagonal entry.
private lemma outside_diagonal (hn : 4 ≤ n) (hd : IsNaturalDerivation d)
    {i j r : Fin n} (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j) :
    d (SpecialLinearGroup.transvection hij 1) r r = 0 := by
  obtain ⟨a, hai, haj, har⟩ := spare hn i j r
  have h := congrArg (fun M => M r r) (chain hd hai.symm haj hij)
  simp only [Matrix.add_apply, left_root, right_root, if_neg hri, if_neg hrj,
    if_neg har.symm, add_zero] at h
  linear_combination -h

private lemma outside_entry (hd : IsNaturalDerivation d)
    {i j k r : Fin n} (hij : i ≠ j) (hkj : k ≠ j) (hri : r ≠ i) (hrk : r ≠ k) :
    d (SpecialLinearGroup.transvection hij 1) r k = 0 := by
  by_cases hrj : r = j
  · subst r
    exact root_row hd hij hkj
  · have h := commutes hd hij hrk.symm hkj.symm hri r r
    simpa only [if_neg hri, if_neg hrk, if_neg hrj, ite_true, zero_add] using h

-- The (i,i) entry of the chain k → i → j, combined with commuting roots.
private lemma corner (hd : IsNaturalDerivation d)
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k) :
    d (SpecialLinearGroup.transvection hkj 1) j j +
      d (SpecialLinearGroup.transvection hij 1) i k = 0 := by
  have hc := commutes hd hik.symm hkj hik hkj.symm k i
  have ht := congrArg (fun M => M i i) (chain hd hik.symm hij hkj)
  have hs := square hd hkj k j
  have h₁ := root_row hd hkj hij
  have h₂ := root_row hd hkj hkj
  have h₃ := root_column hd hkj hik
  simp only [Matrix.add_apply, left_root, right_root, ite_true, if_neg hik,
    if_neg hij, if_neg hkj, if_neg hkj.symm, add_zero] at hc ht hs
  linear_combination (norm := (ring_nf; simp only [CharTwo.two_eq_zero]; ring))
    ht + hc + hs + h₁ + h₂ + h₃

/-- Common-column elementary roots have zero double displacement in every
natural-by-natural matrix derivation in the required higher dimensions.
The two roots are allowed to coincide. -/
theorem naturalDerivation_root_product (hn : 6 ≤ n) (hd : IsNaturalDerivation d)
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) :
    Matrix.single i j 1 * d (SpecialLinearGroup.transvection hkj 1) +
      d (SpecialLinearGroup.transvection hij 1) * Matrix.single k j 1 = 0 := by
  by_cases hik : i = k
  · subst k
    ext r s
    have h := square hd hij r s
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r; subst s; simpa using h
    · subst r; simpa [hs] using h
    · subst s; simpa [hr] using h
    · simp [hr, hs]
  · ext r s
    by_cases hs : s = j
    · subst s
      by_cases hr : r = i
      · subst r
        simpa using corner hd hij hkj hik
      · by_cases hrk : r = k
        · subst r
          simpa [Ne.symm hik] using outside_diagonal (by omega) hd hij (Ne.symm hik) hkj
        · simpa [hr] using outside_entry hd hij hkj hr hrk
    · have hz := root_row hd hkj hs
      by_cases hr : r = i
      · subst r; simp [hs, hz]
      · simp [hr, hs]

end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
