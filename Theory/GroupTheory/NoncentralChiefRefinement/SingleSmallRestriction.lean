module

public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryRestriction
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Sections
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport

/-!
# Restricting a unique small noncentral factor

Intersect a normal series with a smaller actor. The literal intersected
sections inject equivariantly into the original sections. Central sections
therefore contribute no noncentral factors after refinement. A section of
order at most sixteen contributes at most two: every noncentral binary
chief factor has order at least four. Concatenation and Jordan–Hölder give
the same bound for every chief series of the restricted interval.

This uses neither semisimplicity nor a classification of four-dimensional
modules. Source application: Aschbacher–Smith 13.8.31(3), printed p.965.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K] [Finite K]

private theorem count_le_two_of_small_section (s : ChiefSeries K)
    (hc : Nat.card (Section s.head s.last) ≤ 16) : s.noncentralTwoCount ≤ 2 := by
  have hm := section_card_mul s.head s.last (CompositionSeries.head_le _)
  have hb := s.four_pow_noncentralTwoCount_mul_head_le_last
  have hp : 0 < Nat.card s.head.val := Nat.card_pos
  have hpow : 4 ^ s.noncentralTwoCount ≤ Nat.card (Section s.head s.last) := by
    nlinarith
  by_contra hn
  have he := Nat.pow_le_pow_right (by decide : 1 ≤ 4)
    (show 3 ≤ s.noncentralTwoCount by omega)
  norm_num at he
  omega

omit [Finite K] in
private theorem exists_refinement_upper {n : ℕ} (f : Filtration K n)
    (m : Fin n → ℕ)
    (h : ∀ i, ∃ s : ChiefSeries K,
      s.head = f.term i.castSucc ∧ s.last = f.term i.succ ∧ s.noncentralTwoCount ≤ m i) :
    ∃ s : ChiefSeries K, s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      s.noncentralTwoCount ≤ ∑ i, m i := by
  induction n with
  | zero =>
    let s : ChiefSeries K := RelSeries.singleton _ (f.term 0)
    refine ⟨s, rfl, rfl, ?_⟩
    have hz : s.noncentralTwoCount = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun i => Fin.elim0 i.val⟩)
    simpa using hz.le
  | succ n ih =>
    let f' : Filtration K n := ⟨fun i => f.term i.castSucc, fun _ _ h => f.monotone h⟩
    obtain ⟨s, hs0, hs1, hsc⟩ := ih f' (fun i => m i.castSucc) (fun i => h i.castSucc)
    obtain ⟨t, ht0, ht1, htc⟩ := h (Fin.last n)
    have hst : s.last = t.head := hs1.trans ht0.symm
    refine ⟨s.smash t hst, (RelSeries.head_smash hst).trans hs0,
      (RelSeries.last_smash hst).trans ht1, ?_⟩
    rw [ChiefSeries.noncentralTwoCount_smash, Fin.sum_univ_castSucc]
    exact Nat.add_le_add hsc htc

/-- Restriction to a smaller actor of a series whose sole possibly moving
section has order at most sixteen has noncentral count at most two. -/
theorem ChiefSeries.restriction_count_le_two
    (s : ChiefSeries K) (R : Subgroup K) (i : Fin s.length)
    (hc : Nat.card (Section (s i.castSucc) (s i.succ)) ≤ 16)
    (hcentral : ∀ j : Fin s.length, j ≠ i → ∀ r : R, ∀ x,
      sectionAction (s j.castSucc) (s j.succ) r x = x)
    (t : ChiefSeries R)
    (ht0 : t.head = restrictNormalNode R s.head)
    (ht1 : t.last = restrictNormalNode R s.last) : t.noncentralTwoCount ≤ 2 := by
  classical
  let f := s.restrictionFiltration R
  obtain ⟨u, hu0, hu1, hu⟩ := exists_refinement_upper f (fun j => if j = i then 2 else 0) (by
    intro j
    obtain ⟨v, hv0, hv1⟩ := exists_chiefSeries (f.term j.castSucc) (f.term j.succ)
      (f.monotone (Fin.castSucc_le_succ j))
    refine ⟨v, hv0, hv1, ?_⟩
    by_cases he : j = i
    · subst j
      rw [if_pos rfl]
      apply count_le_two_of_small_section
      rw [hv0, hv1]
      exact (Nat.card_le_card_of_injective (restrictionSectionMap R _ _)
        (restrictionSectionMap_injective R _ _)).trans hc
    · rw [if_neg he]
      have hz : IsCentral (f.term j.castSucc) (f.term j.succ) := by
        apply (isCentral_iff_action _ _).mpr
        intro r x
        apply restrictionSectionMap_injective R (s j.castSucc) (s j.succ)
        exact (restrictionSectionMap_equivariant R (s j.castSucc) (s j.succ) r x).trans
          (hcentral j he r _)
      exact (v.noncentralTwoCount_eq_zero_of_central (by rwa [hv0, hv1])).le)
  have he := t.noncentralTwoCount_eq u (ht0.trans hu0.symm) (ht1.trans hu1.symm)
  rw [he]
  simpa using hu

/-- A unique noncentral section for a containing actor, of order sixteen,
cannot give three noncentral factors after restriction to a subgroup. -/
theorem ChiefSeries.restriction_count_le_two_of_unique
    (s : ChiefSeries K) (A R : Subgroup K) (hRA : R ≤ A)
    (hone : s.restrictedNoncentralCount A = 1) (i : Fin s.length)
    (hi : ¬ ∀ a : A, ∀ x, sectionAction (s i.castSucc) (s i.succ) a x = x)
    (hc : Nat.card (Section (s i.castSucc) (s i.succ)) = 16)
    (t : ChiefSeries R)
    (ht0 : t.head = restrictNormalNode R s.head)
    (ht1 : t.last = restrictNormalNode R s.last) : t.noncentralTwoCount ≤ 2 := by
  apply s.restriction_count_le_two R i hc.le _ t ht0 ht1
  intro j hji r x
  have hj : ∀ a : A, ∀ x, sectionAction (s j.castSucc) (s j.succ) a x = x := by
    by_contra hn
    have hsub : Subsingleton {j : Fin s.length //
        ¬ ∀ a : A, ∀ x, sectionAction (s j.castSucc) (s j.succ) a x = x} :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    exact hji (congrArg Subtype.val (hsub.elim ⟨j, hn⟩ ⟨i, hi⟩))
  exact hj ⟨r, hRA r.property⟩ x

end NoncentralChiefRefinement
