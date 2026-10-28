module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Linear
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralPQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Counting
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport
public section
open Classical
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
variable (f : H →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (A : Subgroup H) (hA : IsPGroup 3 A)
    (hAX : A.map f = X)

private theorem step_length {U : Subgroup H} [U.Normal] (hU : IsPGroup 2 U)
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker) (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (hA : IsPGroup 3 A) (hAX : A.map f = X)
    (s : SeriesOn U) (i : Fin s.series.length) :
    sectionCubicLength A (s.lower i).val (s.upper i).val =
      if IsNoncentralTwo (s.lower i) (s.upper i) then 1 else 0 := by
  classical
  let := s.factor_elementary hU i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  have hB : IsPGroup 2 (s.upper i).val :=
    hU.of_injective (inclusion (s.upper_le i)) (inclusion_injective _)
  have he := sectionCubicLength_eq_quotient_of_twoGroup A (s.upper i).val (s.lower i).val
    hA hB (s.series.isChief i).lt.le le_normalizer_of_normal le_normalizer_of_normal
  have heq : sectionCubicLength A (s.lower i).val (s.upper i).val =
      FixedPoints.cubicLength A (s.Factor i) := by
    rw [he]
    apply FixedPoints.cubicLength_eq_of_equivariant (MulEquiv.refl _)
    intro a x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) x
    rfl
  rw [heq]
  by_cases hc : s.Central i
  · rw [if_neg (fun hh => hh.2 hc)]
    apply FixedPoints.cubicLength_eq_zero_of_trivial
    intro a x
    exact (s.central_iff_action i).mp hc a x
  · rw [if_pos ⟨hB.to_quotient _, hc⟩]
    apply simple_group_length_one f hf hp X hX hq A hAX
    · exact s.factor_irreducible i
    · exact fun ht => hc ((s.central_iff_action i).mpr ht)

/-- The actual noncentral binary chief count below a normal two-subgroup
is the fixed-point cubic length, with its original actor. -/
theorem series_count_eq_length (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker) (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (hA : IsPGroup 3 A) (hAX : A.map f = X)
    (s : SeriesOn U) : s.series.noncentralTwoCount = conjugationCubicLength A U := by
  classical
  let w (j : Fin (s.series.length+1)) := conjugationCubicLength A (s.series j).val
  have hi (i : Fin s.series.length) :
      w i.succ = w i.castSucc + if IsNoncentralTwo (s.lower i) (s.upper i) then 1 else 0 := by
    have he := step_length (f:=f) (X:=X) (A:=A) hU hf hp hX hq hA hAX s i
    have hm := conjugationCubicLength_mono A (s.series.isChief i).lt.le
    unfold sectionCubicLength at he
    change w i.succ - w i.castSucc = _ at he
    change w i.castSucc ≤ w i.succ at hm
    omega
  have hs : (∑ i : Fin s.series.length, w i.succ) =
      ∑ i : Fin s.series.length, (w i.castSucc + if IsNoncentralTwo (s.lower i) (s.upper i) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi'
    exact hi i
  rw [Finset.sum_add_distrib] at hs
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
  rw [s.series.noncentralTwoCount_eq_sum]
  change (∑ i : Fin s.series.length, if IsNoncentralTwo (s.lower i) (s.upper i) then 1 else 0) = _
  omega

/-- A complete chief series contributes exactly the lower two-core length when
its terminal quotient has only central binary chief factors. -/
theorem complete_count_eq_length (U : Subgroup H) [U.Normal]
    (hU : IsPGroup 2 U) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (hX : Nat.card X = 3) (hq : IsPGroup 2 (K ⧸ X)) (hA : IsPGroup 3 A)
    (hAX : A.map f = X) (hterm : HasCentralPChiefFactors 2 (H ⧸ U))
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount = conjugationCubicLength A U := by
  obtain ⟨r⟩ := SeriesOn.exists_series U
  have hr0 := r.head_eq
  have hrl := r.last_eq
  obtain ⟨t, ht0, htl⟩ : ∃ t : ChiefSeries H, t.head = ⟨U, inferInstanceAs U.Normal⟩ ∧ t.last = ⊤ :=
    exists_chiefSeries ⟨U, inferInstanceAs U.Normal⟩ ⊤ le_top
  have hrt : r.series.last = t.head := hrl.trans ht0.symm
  have hupper : t.noncentralTwoCount = 0 :=
    ChiefSeries.noncentralTwoCount_eq_zero_of_centralTwo_quotient t
      ⟨U, inferInstanceAs U.Normal⟩ ht0.ge hterm
  have hcount := series_count_eq_length (f:=f) (X:=X) (A:=A)
    U hU hf hp hX hq hA hAX r
  have hsmash : ChiefSeries.noncentralTwoCount (r.series.smash t hrt) =
      r.series.noncentralTwoCount + t.noncentralTwoCount :=
    ChiefSeries.noncentralTwoCount_smash r.series t hrt
  have hseries : s.noncentralTwoCount = ChiefSeries.noncentralTwoCount (r.series.smash t hrt) :=
    s.noncentralTwoCount_eq _
      (h0.trans ((RelSeries.head_smash hrt).trans hr0).symm)
      (h1.trans ((RelSeries.last_smash hrt).trans htl).symm)
  rw [hseries, hsmash, hupper, add_zero, hcount]
end NoncentralChiefRefinement.CubicComparison
