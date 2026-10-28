module
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupAction.NoncentralTwoChiefLength.Native

/-!
# Cubic movement bounded by small chief factors

Coprime fixed-point lifting makes the cubic movement length additive
along an actual normal chief series in a two-group. Central factors
contribute zero; factors of order at most sixteen contribute at most
two. Telescoping therefore bounds the whole action by twice the number
of noncentral factors, without assuming the series splits.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.967,
the bound on the L₁ action on V_H/U_H.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H] {U : Subgroup H} [U.Normal]

/-- Any three-subgroup has cubic movement length at most twice the number
of noncentral chief factors when those factors have order at most sixteen. -/
theorem SeriesOn.cubic_length_le_twice_count (s : SeriesOn U) (hU : IsPGroup 2 U)
    (hcard : ∀ i, ¬ s.Central i → Nat.card (s.Factor i) ≤ 16)
    (A : Subgroup H) (hA : IsPGroup 3 A) :
    conjugationCubicLength A U ≤ 2 * s.noncentralCount := by
  classical
  let w (j : Fin (s.series.length+1)) := conjugationCubicLength A (s.series j).val
  have hi (i : Fin s.series.length) :
      w i.succ ≤ w i.castSucc + 2 * (if s.Central i then 0 else 1) := by
    have hB : IsPGroup 2 (s.upper i).val := hU.to_le (s.upper_le i)
    let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
    let := μ
    have he := sectionCubicLength_eq_quotient_of_twoGroup A (s.upper i).val (s.lower i).val
      hA hB (s.series.isChief i).lt.le le_normalizer_of_normal le_normalizer_of_normal
    have heq : sectionCubicLength A (s.lower i).val (s.upper i).val =
        FixedPoints.cubicLength A (s.Factor i) := by
      rw [he]
      apply FixedPoints.cubicLength_eq_of_equivariant (MulEquiv.refl _)
      intro a x
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) x
      rfl
    have hb : FixedPoints.cubicLength A (s.Factor i) ≤ 2 * (if s.Central i then 0 else 1) := by
      by_cases hc : s.Central i
      · rw [if_pos hc, mul_zero]
        exact (FixedPoints.cubicLength_eq_zero_of_trivial
          (fun (a : A) x => (s.central_iff_action i).mp hc a x)).le
      · rw [if_neg hc, mul_one]
        have hh := Nat.log_mono_right
          ((Nat.le_of_dvd Nat.card_pos (FixedPoints.subgroup A (s.Factor i)).index_dvd_card).trans
            (hcard i hc)) (b := 4)
        exact hh
    rw [← heq] at hb
    have hm := conjugationCubicLength_mono A (s.series.isChief i).lt.le
    unfold sectionCubicLength at hb
    change w i.succ - w i.castSucc ≤ _ at hb
    change w i.castSucc ≤ w i.succ at hm
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht : (∑ i : Fin s.series.length, w i.succ) + w 0 =
      (∑ i : Fin s.series.length, w i.castSucc) + w (Fin.last s.series.length) := by
    rw [add_comm _ (w 0), ← Fin.sum_univ_succ, ← Fin.sum_univ_castSucc]
  have hz : w 0 = 0 := by
    change conjugationCubicLength A s.series.head.val = 0
    rw [s.head_eq]
    exact conjugationCubicLength_bot A
  have hl : w (Fin.last s.series.length) = conjugationCubicLength A U := by
    change conjugationCubicLength A s.series.last.val = _
    rw [s.last_eq]
  have hc : (∑ i : Fin s.series.length, if s.Central i then 0 else 1) = s.noncentralCount := by
    rw [SeriesOn.noncentralCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [ite_not, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun i => ¬ s.Central i) Finset.univ)
  omega
end NoncentralChiefRefinement
