module
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.PrimeRankElementary
/-!
# Square roots in rank-one two-groups

A finite two-group of rank at most one has a unique involution. If its
order exceeds two, some element has order at least four: otherwise the
whole group is elementary and violates the rank bound. A suitable power
has order four, and its square is the specified involution.

This elementary part of the cyclic/generalized-quaternion argument is
used for the point-core actor in Aschbacher–Smith 14.7.15(2), p.1047.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace IsPGroup
/-- In a rank-one two-group of order greater than two, the involution is a square. -/
theorem exists_square_root_of_rank_one
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    (hr : primeRank 2 R ≤ 1) (hc : 2 < Nat.card R)
    (z : R) (hz : z ≠ 1) (hz2 : z^2=1) :
    ∃ b : R, b^2=z ∧ orderOf b=4 := by
  classical
  let : Nontrivial R := nontrivial_of_ne z 1 hz
  have hbound := (primeRank_le_iff_elementary_card_le R).mp hr
  obtain ⟨t,ht,_,huniq⟩ := hR.exists_central_involution_of_no_elementary_four
    (fun E hE hcard => by have hh := hbound E hE; norm_num [hcard] at hh)
  have hzt : z=t := (huniq z hz2).resolve_left hz
  have hn : ¬ ∀ x : R, x^2=1 := by
    intro hh
    let : IsMulCommutative R := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hh x)) a b).eq⟩⟩
    let : IsElementaryAbelian 2 R :=
      { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hh }
    have htop : IsElementaryAbelian 2 (⊤ : Subgroup R) :=
      { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
          (fun x => Subtype.ext (hh x)) }
    have hb := hbound ⊤ htop
    rw [card_top,pow_one] at hb
    omega
  push Not at hn
  obtain ⟨x,hx⟩ := hn
  obtain ⟨n,hn⟩ := hR.exists_orderOf_eq_pow x
  have hn2 : 2 ≤ n := by
    by_contra! hsmall
    interval_cases n
    · have he : x=1 := orderOf_eq_one_iff.mp hn
      exact hx (by rw [he,one_pow])
    · exact hx (by simpa only [hn,pow_one] using pow_orderOf_eq_one x)
  have hd : 4 ∣ orderOf x := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  let b := x^(orderOf x/4)
  have hb : orderOf b=4 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hd
  have hb4 : b^4=1 := hb ▸ pow_orderOf_eq_one b
  have hb2 : b^2≠1 := by
    intro hh
    have hh' := orderOf_dvd_of_pow_eq_one hh
    norm_num [hb] at hh'
  have hbt : b^2=t := (huniq (b^2) (by simpa only [←pow_mul] using hb4)).resolve_left hb2
  exact ⟨b,hbt.trans hzt.symm,hb⟩
end IsPGroup
