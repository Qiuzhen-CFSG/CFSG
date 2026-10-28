module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

/-!
# The integral Gram calculation for the four induced virtual characters

After removing the principal constituent, the four induced rows have norm
two, mutual scalar product one, and degree minus one. Positive irreducible
degrees force each row to be a difference of two basis vectors. The common
Gram matrix then forces one common constituent and four distinct others.
-/

public section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion

private theorem norm_two_degree_neg_one {J : Type*} [Fintype J] [DecidableEq J]
    (v : J → ℤ) (d : J → ℕ) (hd : ∀ j, 0 < d j)
    (hn : ∑ j, v j ^ 2 = 2) (hw : ∑ j, v j * (d j : ℤ) = -1) :
    ∃ a b : J, a ≠ b ∧
      ∀ j, v j = (if j = a then 1 else 0) - (if j = b then 1 else 0) := by
  classical
  have hs (j : J) : v j = 0 ∨ v j = 1 ∨ v j = -1 := by
    have hb : v j ^ 2 ≤ 2 := by
      exact (Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)).trans_eq hn
    have hlo : -1 ≤ v j := by nlinarith
    have hhi : v j ≤ 1 := by nlinarith
    omega
  let S := Finset.univ.filter fun j => v j ≠ 0
  have hS : (S.card : ℤ) = 2 := by
    calc
      (S.card : ℤ) = ∑ j ∈ S, (1 : ℤ) := by simp
      _ = ∑ j ∈ S, v j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hne : v j ≠ 0 := (Finset.mem_filter.mp hj).2
        rcases (hs j).resolve_left hne with h | h <;> simp [h]
      _ = ∑ j, v j ^ 2 := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hz : v j = 0 := by simpa [S] using hj
        simp [hz]
      _ = 2 := hn
  have hc : S.card = 2 := by exact_mod_cast hS
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hc
  have hva : v a ≠ 0 := by
    have : a ∈ S := by rw [hSab]; simp
    exact (Finset.mem_filter.mp this).2
  have hvb : v b ≠ 0 := by
    have : b ∈ S := by rw [hSab]; simp
    exact (Finset.mem_filter.mp this).2
  have hz (j : J) (hja : j ≠ a) (hjb : j ≠ b) : v j = 0 := by
    by_contra h
    have : j ∈ S := by simp [S, h]
    simp [hSab, hja, hjb] at this
  have hdeg : v a * (d a : ℤ) + v b * (d b : ℤ) = -1 := by
    rw [← hw]
    symm
    calc
      _ = ∑ j ∈ ({a,b} : Finset J), v j * (d j : ℤ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        simp [hz j hj.1 hj.2]
      _ = _ := by rw [Finset.sum_pair hab]
  have hda : (0 : ℤ) < d a := by exact_mod_cast hd a
  have hdb : (0 : ℤ) < d b := by exact_mod_cast hd b
  rcases (hs a).resolve_left hva with ha | ha <;>
    rcases (hs b).resolve_left hvb with hb | hb
  · rw [ha, hb] at hdeg
    omega
  · refine ⟨a, b, hab, fun j => ?_⟩
    by_cases hja : j = a
    · subst j; simp [ha, hab]
    by_cases hjb : j = b
    · subst j; simp [hb, hab.symm]
    simp [hja, hjb, hz j hja hjb]
  · refine ⟨b, a, hab.symm, fun j => ?_⟩
    by_cases hja : j = a
    · subst j; simp [ha, hab]
    by_cases hjb : j = b
    · subst j; simp [hb, hab.symm]
    simp [hja, hjb, hz j hja hjb]
  · rw [ha, hb] at hdeg
    omega

private theorem pair_dot {J : Type*} [Fintype J] [DecidableEq J]
    (a b c d : J) :
    (∑ j : J, ((if j = a then 1 else 0) - (if j = b then 1 else 0)) *
      ((if j = c then 1 else 0) - (if j = d then 1 else 0)) : ℤ) =
    (if a = c then 1 else 0) + (if b = d then 1 else 0) -
      (if a = d then 1 else 0) - (if b = c then 1 else 0) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero, mul_one]
  simp only [eq_comm]
  ring

/-- Four integral rows of norm two, pairwise product one, and degree minus
one share exactly one constituent. All other constituents are distinct. -/
theorem four_rows_common_constituent {J : Type*} [Fintype J] [DecidableEq J]
    (v : Fin 4 → J → ℤ) (d : J → ℕ) (hd : ∀ j, 0 < d j)
    (hn : ∀ i, ∑ j, v i j ^ 2 = 2)
    (hw : ∀ i, ∑ j, v i j * (d j : ℤ) = -1)
    (hp : ∀ i k, i ≠ k → ∑ j, v i j * v k j = 1) :
    ∃ (ε : ℤ) (a : J) (b : Fin 4 → J),
      (ε = 1 ∨ ε = -1) ∧ Function.Injective b ∧ (∀ i, a ≠ b i) ∧
      ∀ i j, v i j = ε * ((if j = a then 1 else 0) - (if j = b i then 1 else 0)) := by
  classical
  choose a b hab hv using fun i => norm_two_degree_neg_one (v i) d hd (hn i) (hw i)
  have hdot (i k : Fin 4) (hik : i ≠ k) :
      (if a i = a k then 1 else 0) + (if b i = b k then 1 else 0) -
        (if a i = b k then 1 else 0) - (if b i = a k then 1 else 0) = (1 : ℤ) := by
    rw [← pair_dot]
    simpa only [hv] using hp i k hik
  have hshare (i k : Fin 4) (hik : i ≠ k) : a i = a k ∨ b i = b k := by
    have h := hdot i k hik
    by_contra! hne
    simp only [if_neg hne.1, if_neg hne.2, zero_add] at h
    split_ifs at h <;> omega
  have hnotboth (i k : Fin 4) (hik : i ≠ k) : ¬ (a i = a k ∧ b i = b k) := by
    rintro ⟨ha, hb⟩
    have h := hdot i k hik
    rw [ha, hb, if_pos rfl, if_pos rfl, if_neg (hab k), if_neg (hab k).symm] at h
    omega
  rcases hshare 0 1 (by decide) with haa | hbb
  · have hbb : b 0 ≠ b 1 := fun h => hnotboth 0 1 (by decide) ⟨haa,h⟩
    have hconst (i : Fin 4) : a i = a 0 := by
      by_cases hi0 : i = 0
      · subst i; rfl
      by_cases hi1 : i = 1
      · subst i; exact haa.symm
      rcases hshare i 0 hi0 with h | h
      · exact h
      rcases hshare i 1 hi1 with h' | h'
      · exact h'.trans haa.symm
      exact (hbb (h.symm.trans h')).elim
    refine ⟨1, a 0, b, Or.inl rfl, ?_, ?_, ?_⟩
    · intro i k hik
      by_contra hne
      exact hnotboth i k hne ⟨(hconst i).trans (hconst k).symm,hik⟩
    · intro i
      rw [← hconst i]
      exact hab i
    · intro i j
      simpa only [hconst i, one_mul] using hv i j
  · have haa : a 0 ≠ a 1 := fun h => hnotboth 0 1 (by decide) ⟨h,hbb⟩
    have hconst (i : Fin 4) : b i = b 0 := by
      by_cases hi0 : i = 0
      · subst i; rfl
      by_cases hi1 : i = 1
      · subst i; exact hbb.symm
      rcases hshare i 0 hi0 with h | h
      · rcases hshare i 1 hi1 with h' | h'
        · exact (haa (h.symm.trans h')).elim
        · exact h'.trans hbb.symm
      · exact h
    refine ⟨-1, b 0, a, Or.inr rfl, ?_, ?_, ?_⟩
    · intro i k hik
      by_contra hne
      exact hnotboth i k hne ⟨hik,(hconst i).trans (hconst k).symm⟩
    · intro i
      rw [← hconst i]
      exact (hab i).symm
    · intro i j
      rw [hv i j, hconst i]
      ring

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion
