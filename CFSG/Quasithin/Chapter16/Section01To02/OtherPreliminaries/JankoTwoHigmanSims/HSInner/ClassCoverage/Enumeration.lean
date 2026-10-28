module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.SylowElementConjugacy
import Mathlib.Tactic.FinCases

/-!
# Exhaustive inner involution fusion in the fixed HS carrier

The checked word tree identifies 512 distinct carrier elements. Right
multiplication by the generators and their inverses proves that these exhaust
the given candidate subgroup. Its order and the known carrier order make it a
Sylow two-subgroup. The finite conjugating words fuse each of its involutions
to `e0` or `t`; Sylow conjugacy supplies exhaustive ambient coverage.

This argument needs no centralizer-order, simplicity or classification premise,
and does not enumerate normal elementary subgroups of the Sylow subgroup.
Source: ATLAS HSG1-p100B0; GLS3 Table 5.3m; Aschbacher–Smith 16.1.5(10), p.1172.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

namespace Certificate

theorem element_zero : element 0 = 1 := rfl

theorem value_spec (i : Fin 512) (p : Fin 100) :
    inclusion (element i) p = value i p := by
  have aux : ∀ (n : ℕ) (j : Fin 512), j.val = n → ∀ q : Fin 100,
      inclusion (element j) q = value j q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        simpa only [element_zero, map_one, Equiv.Perm.one_apply] using (value_zero q).symm
      obtain ⟨hlt, hw, hn⟩ := word_data j hzero
      have hp := ih (parent j).val (hj ▸ hlt) (parent j) rfl
      have he : element j = element (parent j) * localLetter (parentLetter j) := by
        simp only [element, hw, evalWord_append, evalWord, mul_one]
      rw [he, map_mul]
      change inclusion (element (parent j))
        (inclusion (localLetter (parentLetter j)) q) = value j q
      rw [hp, ← localValue_spec, ← value_step, hn]
  exact aux i.val i rfl p

theorem element_step (i : Fin 512) (s : Fin 4) :
    element i * localLetter s = element (next i s) := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  intro p
  rw [map_mul]
  change inclusion (element i) (inclusion (localLetter s) p) = inclusion (element (next i s)) p
  rw [value_spec, value_spec, ← localValue_spec, value_step]

theorem element_injective : Function.Injective element := by
  intro i j h
  have h1 : value i 1 = value j 1 := by rw [← value_spec, ← value_spec, h]
  have h4 : value i 4 = value j 4 := by rw [← value_spec, ← value_spec, h]
  rw [← decode_value i, h1, h4, decode_value]

private theorem localLetter_mem (s : Fin 4) : localLetter s ∈ subgroup := by
  have h (j : Fin 3) : sylowGenerator j ∈ subgroup := subset_closure ⟨j, rfl⟩
  fin_cases s
  · exact h 0
  · exact h 1
  · exact h 2
  · exact Subgroup.inv_mem _ (h 2)

private theorem closure_localLetter : closure (Set.range localLetter) = subgroup := by
  apply le_antisymm
  · exact (closure_le _).mpr (by rintro _ ⟨s, rfl⟩; exact localLetter_mem s)
  · apply (closure_le _).mpr
    rintro _ ⟨s, rfl⟩
    fin_cases s
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
    · exact subset_closure ⟨2, rfl⟩

theorem element_mem (i : Fin 512) : element i ∈ subgroup := by
  have hw (w : List (Fin 4)) : evalWord localLetter w ∈ subgroup := by
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons s w ih => exact Subgroup.mul_mem _ (localLetter_mem s) ih
  exact hw (words i)

theorem element_cover (x : Carrier) (hx : x ∈ subgroup) :
    ∃ i : Fin 512, x = element i := by
  rw [← closure_localLetter] at hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, element_zero.symm⟩
  | mul_right x _ y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨next i s, element_step i s⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    rw [← localLetter_inv]
    exact ⟨next i (invLetter s), element_step i (invLetter s)⟩

/-- The finite certificates compute the order of the actual candidate subgroup. -/
theorem subgroup_card : Nat.card subgroup = 512 := by
  let f : Fin 512 → subgroup := fun i => ⟨element i, element_mem i⟩
  have hi : Function.Injective f := fun _ _ h => element_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := element_cover x x.property
    exact ⟨i, Subtype.ext hi.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_fin 512)

theorem subgroup_index : subgroup.index = 86625 := by
  have h := subgroup.card_mul_index
  rw [subgroup_card, NormalizerIndex.card_carrier] at h
  omega

/-- A concrete Sylow subgroup, obtained from the checked 512-element enumeration. -/
def sylow : Sylow 2 Carrier :=
  (show IsPGroup 2 subgroup from
    IsPGroup.of_card (n := 9) (by norm_num [subgroup_card])).toSylow
    (by rw [subgroup_index]; decide)

theorem involution_fusion (i : Fin 512) (hsq : element i ^ 2 = 1) (hne : element i ≠ 1) :
    IsConj e0 (element i) ∨ IsConj t (element i) := by
  have hi : i ≠ 0 := by rintro rfl; exact hne element_zero
  have hp : value i (value i (badPoint i)) = badPoint i := by
    have hh := congrArg (fun x : Carrier => inclusion x (badPoint i)) hsq
    simpa only [pow_two, map_mul, Equiv.Perm.mul_apply, value_spec,
      map_one, Equiv.Perm.one_apply] using hh
  let g := evalWord ambientLetter (fusionWord i)
  have hg : g * element i = base i * g := by
    apply Sporadic.LeechRelated.HS.inclusion_injective
    apply Equiv.ext
    intro p
    simpa only [g, map_mul, Equiv.Perm.mul_apply, value_spec, ← wordValue_spec,
      ← baseValue_spec] using fusion_value i hi hp p
  have hc : IsConj (base i) (element i) :=
    (isConj_iff.mpr ⟨g, (mul_inv_eq_iff_eq_mul).mpr hg⟩).symm
  by_cases h : fusionA i = true
  · exact Or.inl (by simpa only [base, h, ↓reduceIte] using hc)
  · exact Or.inr (by simpa only [base, h, Bool.false_eq_true, ↓reduceIte] using hc)

end Certificate

/-- Exhaustive conjugacy coverage of involutions in the exact HS carrier. -/
theorem involution_classes (x : Carrier) (hx : orderOf x = 2) :
    IsConj e0 x ∨ IsConj t x := by
  obtain ⟨y, hy⟩ := Certificate.sylow.exists_isConj_of_orderOf_eq_prime_pow
    (hx.trans (pow_one 2).symm)
  obtain ⟨i, hi⟩ := Certificate.element_cover y y.property
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have he : (MulAut.conj g) x = Certificate.element i := hg.trans hi
  have hsq : Certificate.element i ^ 2 = 1 := by
    rw [← he, ← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
  have hne : Certificate.element i ≠ 1 := by
    intro h
    exact (orderOf_eq_prime_iff.mp hx).2
      ((MulAut.conj g).injective (he.trans (h.trans (map_one _).symm)))
  have hc : IsConj x (Certificate.element i) := isConj_iff.mpr ⟨g, he⟩
  rcases Certificate.involution_fusion i hsq hne with h | h
  · exact Or.inl (h.trans hc.symm)
  · exact Or.inr (h.trans hc.symm)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
