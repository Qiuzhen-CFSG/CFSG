module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Marked
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Point

/-!
# Conditional assembly of the Hermitian tensor ratios

The earlier H.4.4 inputs here are exactly the root codimension and its inner
large-rank clause, with root conjugacy retained in the first input. A small
inner actor has rank greater than n, so the latter clause forces codimension
at least 5n. Comparing with the two-rank bound 4n forces equality in both
bounds. In a marked Sylow the actor is then a full radical; the point
radical has ratio two, leaving precisely the plane radical of ratio 5/4.

Two additional inputs remain to be proved from the actual actions: exclusion
of outer elementary actors at ratio 5/4 (and outer quadratic actors at two),
and the rank bound n for inner quadratic actors. The final quadratic
contradiction compares that bound with root codimension 4n. These are
conditional assembly theorems, not completed source theorems.

The printed claim in K.3.2.4 that the root moved space has rank 5n conflicts
with the literal action: its moved rank is 4n and its fixed rank is 5n.
H.4.4(2) concerns the centralizer of the fixed space. No identification of
that centralizer with the moved-space centralizer is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467, using H.4.4(2–3), printed pp.380–381.
-/

@[expose] public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

/-- H.4.4(2)'s root codimension, transported to the actual inner involutions.
The parent discharges this earlier input, including root conjugacy. -/
def InnerRootDimensions : Prop :=
  ∀ i : M, i ∈ innerActor n M → orderOf i = 2 →
    fixedCodim (overgroupAction n M) (Subgroup.zpowers i) = 4 * n

/-- Precisely the inner branch of H.4.4(3), retained as an earlier-source input. -/
def InnerLargeRankCodimension : Prop :=
  ∀ A : Subgroup M, IsElementaryTwo A → A ≤ innerActor n M → n < rank A →
    5 * n ≤ fixedCodim (overgroupAction n M) A

omit hM in
theorem four_mul_le_inner_codim (hroot : InnerRootDimensions n M)
    (A : Subgroup M) (hA : IsElementaryTwo A) (hAI : A ≤ innerActor n M) :
    4 * n ≤ fixedCodim (overgroupAction n M) A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨i, hi⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  have hi2 : orderOf (i : M) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (i : M) i.property)
    (fun h => hi (Subtype.ext h))
  have hfix : fixedSpace (overgroupAction n M) A ≤
      fixedSpace (overgroupAction n M) (Subgroup.zpowers (i : M)) := by
    intro X hX
    exact (mem_fixedSpace_zpowers_iff _ _ X).mpr (hX i)
  have hdim := Submodule.finrank_mono hfix
  have hsumA := fixedCodim_add_finrank (overgroupAction n M) A
  have hsumI := fixedCodim_add_finrank (overgroupAction n M) (Subgroup.zpowers (i : M))
  have hiDim := hroot i (hAI i.property) hi2
  omega

omit hM in
theorem small_ratio_iff (A : Subgroup M) (hA : IsElementaryTwo A) :
    actionRatio (overgroupAction n M) A ≤ 5 / 4 ↔
      4 * fixedCodim (overgroupAction n M) A ≤ 5 * rank A := by
  have hr : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.rank_pos.ne'
  rw [actionRatio, ENNReal.div_le_iff hr (by simp)]
  have he : (5 / 4 : ℝ≥0∞) * rank A = (5 * rank A) / 4 := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [he, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_cast
  omega

include hM in
/-- H.4.4(3) makes a small inner actor maximal in rank. No root-intersection
or unproved fixed-space centralizer is substituted for that source clause. -/
theorem small_inner_rank_codim (hroot : InnerRootDimensions n M)
    (hlarge : InnerLargeRankCodimension n M)
    (A : Subgroup M) (hA : IsElementaryTwo A) (hAI : A ≤ innerActor n M)
    (hr : actionRatio (overgroupAction n M) A ≤ 5 / 4) :
    rank A = 4 * n ∧ fixedCodim (overgroupAction n M) A = 5 * n := by
  have hc := four_mul_le_inner_codim n M hroot A hA hAI
  have hr' := (small_ratio_iff n M A hA).mp hr
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hbig : n < rank A := by omega
  have hlargeA := hlarge A hA hAI hbig
  have hbound := elementary_rank_le n M hM A hA
  omega

/-- The full maximal-rank alternatives in the marked unipotent group. -/
theorem rank_four_eq_radical (A : Subgroup M) (hA : IsElementaryTwo A)
    (hAU : A ≤ unipotentActor n M hM) (hr : rank A = 4 * n) :
    A = pointActor n M hM ∨ A = planeActor n M hM := by
  rcases elementary_le_radical n M hM A hA hAU with hp | hp
  · left
    apply Subgroup.eq_of_le_of_card_ge hp
    rw [card_pointActor, hA.card_eq_two_pow_rank, hr]
  · right
    apply Subgroup.eq_of_le_of_card_ge hp
    rw [card_planeActor, hA.card_eq_two_pow_rank, hr]

/-- Conditional assembly of the minimizing actor in the marked Sylow.
Only the genuine earlier H.4.4 dimension inputs and the separate exclusion
of outer actors remain explicit. -/
theorem small_actor_eq_plane (hroot : InnerRootDimensions n M)
    (hlarge : InnerLargeRankCodimension n M)
    (houter : ∀ A : Subgroup M, IsElementaryTwo A →
      actionRatio (overgroupAction n M) A ≤ 5 / 4 → A ≤ innerActor n M)
    (T : Sylow 2 M) (hT : IsMarkedSylow n M hM T)
    (A : Subgroup M) (hA : IsElementaryTwo A) (hAT : A ≤ T)
    (hr : actionRatio (overgroupAction n M) A ≤ 5 / 4) :
    A = planeActor n M hM := by
  have hAI := houter A hA hr
  obtain ⟨hrank,_⟩ := small_inner_rank_codim n M hM hroot hlarge A hA hAI hr
  have hAU : A ≤ unipotentActor n M hM := by
    rw [← hT]
    exact le_inf hAT hAI
  rcases rank_four_eq_radical n M hM A hA hAU hrank with hp | hp
  · have hc := (small_ratio_iff n M A hA).mp hr
    rw [hp, codim_point_fixed, rank_pointActor] at hc
    have hn := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  · exact hp

include hM in
/-- Conditional cubic-ratio assembly with a constructed attaining actor. -/
theorem cubicRatio_eq_of_inner_dimensions
    (hroot : InnerRootDimensions n M) (hlarge : InnerLargeRankCodimension n M)
    (houter : ∀ A : Subgroup M, IsElementaryTwo A →
      actionRatio (overgroupAction n M) A ≤ 5 / 4 → A ≤ innerActor n M) :
    cubicRatio (overgroupAction n M) = 5 / 4 := by
  apply le_antisymm (cubicRatio_le_five_fourths n M hM)
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  by_cases hr : actionRatio (overgroupAction n M) A ≤ 5 / 4
  · obtain ⟨hrank,hcodim⟩ := small_inner_rank_codim n M hM hroot hlarge A hA.1
      (houter A hA.1 hr) hr
    have he : actionRatio (overgroupAction n M) A = 5 / 4 := by
      rw [actionRatio, hcodim, hrank, Nat.cast_mul, Nat.cast_mul]
      have hn : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
      rw [ENNReal.mul_div_mul_right _ _ hn (by simp)]
      norm_num
    exact he.ge
  · exact (lt_of_not_ge hr).le

omit hM in
/-- Once actual outer actions and the inner quadratic calculation have been
supplied, the root displacement 4n contradicts ratio at most two. -/
theorem quadraticRatio_gt_two_of_inner_rank
    (hroot : InnerRootDimensions n M)
    (houter : ∀ A : Subgroup M, IsElementaryTwo A → IsQuadratic (overgroupAction n M) A →
      actionRatio (overgroupAction n M) A ≤ 2 → A ≤ innerActor n M)
    (hquad : ∀ A : Subgroup M, IsElementaryTwo A → A ≤ innerActor n M →
      IsQuadratic (overgroupAction n M) A → rank A ≤ n) :
    2 < quadraticRatio (overgroupAction n M) := by
  by_contra! h
  obtain ⟨A,hA,hq,hr⟩ := (quadraticRatio_le_iff _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mp h
  have hAI := houter A hA hq hr
  have hd := four_mul_le_inner_codim n M hroot A hA hAI
  have hb := hquad A hA hAI hq
  have hc := (actionRatio_le_nat_iff (overgroupAction n M) hA 2).mp hr
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

/-- The set of small elementary actors in the marked Sylow is exactly the
singleton on Q_W, once the indicated source inputs have been discharged. -/
theorem small_actor_iff_eq_plane (hroot : InnerRootDimensions n M)
    (hlarge : InnerLargeRankCodimension n M)
    (houter : ∀ A : Subgroup M, IsElementaryTwo A →
      actionRatio (overgroupAction n M) A ≤ 5 / 4 → A ≤ innerActor n M)
    (T : Sylow 2 M) (hT : IsMarkedSylow n M hM T) (A : Subgroup M) :
    (IsElementaryTwo A ∧ A ≤ T ∧ actionRatio (overgroupAction n M) A ≤ 5 / 4) ↔
      A = planeActor n M hM := by
  constructor
  · rintro ⟨hA,hAT,hr⟩
    exact small_actor_eq_plane n M hM hroot hlarge houter T hT A hA hAT hr
  · rintro rfl
    exact ⟨planeActor_elementary n M hM, planeActor_le_markedSylow n M hM T hT,
      (planeActor_ratio n M hM).le⟩

end CFSG.Quasithin.ChapterK.Linear.Tensor
