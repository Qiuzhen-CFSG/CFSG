module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry
public import Theory.SpecificGroups.PSL5Two.TwoRankUpper
public import Theory.GroupTheory.PrimeRankHom


/-!
# The full automorphism two-rank of PSL₅(2)

Every elementary subgroup of the full automorphism group is either inner
or contains an outer involution. In the latter case, centerlessness lifts
its inner kernel faithfully into the actual fixed group of that involution.
The checked symmetric-form normalization and fixed-group construction identify
this group with S₆. Its order 720 bounds the kernel's two-rank by four, and
the cyclic outer quotient contributes at most one more generator.

Thus elementary subgroups meeting the graph coset have rank at most five.
The inner group has two-rank six, attained by its upper-right 2-by-3 block.
Transport through the genuine projective-to-linear equivalence gives both
the upper bound and equality for the full automorphism group of PSL₅(2).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the two-rank
inspection in the proof of G.9.3, printed p.356 (PDF p.367). The outer-involution
fixed-group calculation is the existing degree-five geometry used in E.6.23.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic
namespace BinaryLinear.AutomorphismTwoRank

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
    DFunLike.coe_injective

private theorem five_center_eq_bot : center (LinearGroup 5) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((centerCongr (slEquivLinear 5)).symm ⟨x, hx⟩).property
  change (slEquivLinear 5).symm x ∈ center _ at h
  rw [binary_center_eq_bot (by decide : 0 < 5), mem_bot] at h
  exact mem_bot.mpr ((slEquivLinear 5).symm.map_eq_one_iff.mp h)

private noncomputable def fiveInnerEquiv :
    LinearGroup 5 ≃* MulAut.innerSubgroup (LinearGroup 5) :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot five_center_eq_bot)

private theorem symmetric_six_rank_le_four : primeRank 2 (Equiv.Perm (Fin 6)) ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hd : 2 ^ n ∣ 720 := by
    have h := E.card_subgroup_dvd_card
    rw [hn, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
    exact h
  have hle : n ≤ 4 := by
    by_contra! h
    have : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 (by omega : 5 ≤ n)).trans hd
    norm_num at this
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hle

private theorem five_outer_fixed_rank_le_four
    (a : MulAut (LinearGroup 5)) (ha : a ^ 2 = 1)
    (hout : a ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    primeRank 2 a.fixedSubgroup ≤ 4 := by
  obtain ⟨m⟩ := SixSylowActors.Five.exists_fixedModel a ha hout
  rw [primeRank_equiv 2 m.equiv]
  exact symmetric_six_rank_le_four

/-- The inner kernel of an elementary group meeting the graph coset embeds
in the fixed S₆ of any chosen outer involution, so its two-rank is at most four. -/
theorem five_outer_elementary_kernel_rank_le
    (E : Subgroup (MulAut (LinearGroup 5))) [IsElementaryAbelian 2 E]
    (a : MulAut (LinearGroup 5)) (haE : a ∈ E)
    (hout : a ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    primeRank 2 ((QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 5))).comp
      E.subtype).ker ≤ 4 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 5))
  let f := q.comp E.subtype
  let k : f.ker →* MulAut.innerSubgroup (LinearGroup 5) :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := fiveInnerEquiv.symm.toMonoidHom.comp k
  have hg (x : f.ker) : MulAut.conj (g x) = x.1.1 := by
    exact congrArg Subtype.val (fiveInnerEquiv.apply_symm_apply (k x))
  have hfixed (x : f.ker) : g x ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply MulAut.conj_injective_of_center_eq_bot five_center_eq_bot
    have he : MulAut.conj (a (g x)) = a * MulAut.conj (g x) * a⁻¹ := by
      ext y
      simp
    rw [he, hg]
    have hc : a * x.1.1 = x.1.1 * a :=
      congrArg Subtype.val (mul_comm (⟨a, haE⟩ : E) x.1)
    rw [hc, mul_inv_cancel_right]
  let j : f.ker →* a.fixedSubgroup := g.codRestrict _ hfixed
  have hj : Function.Injective j := by
    intro x y hxy
    have h := congrArg (fun z : a.fixedSubgroup => MulAut.conj (z : LinearGroup 5)) hxy
    change MulAut.conj (g x) = MulAut.conj (g y) at h
    rw [hg, hg] at h
    exact Subtype.ext (Subtype.ext h)
  exact (primeRank_le_of_injective 2 j hj).trans
    (five_outer_fixed_rank_le_four a (elemPow_eq_one_of_isElementaryAbelian a haE) hout)

/-- An elementary subgroup containing a noninner automorphism has rank at most five. -/
theorem five_outer_elementary_rank_le
    (E : Subgroup (MulAut (LinearGroup 5))) [IsElementaryAbelian 2 E]
    (hE : ¬ E ≤ MulAut.innerSubgroup (LinearGroup 5)) : primeRank 2 E ≤ 5 := by
  obtain ⟨a, haE, hout⟩ := SetLike.not_le_iff_exists.mp hE
  have hk := five_outer_elementary_kernel_rank_le E a haE hout
  let : IsCyclic (MulAut.Outer (LinearGroup 5)) := linear_outer_isCyclic (Or.inr rfl)
  have ho : primeRank 2 (MulAut.Outer (LinearGroup 5)) ≤ 1 := by
    let P : Sylow 2 (MulAut.Outer (LinearGroup 5)) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic inferInstance
  have hr := primeRank_le_ker_add (p := 2)
    ((QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 5))).comp E.subtype)
  exact hr.trans (Nat.add_le_add hk ho)

private theorem five_linear_automorphism_rank_le : primeRank 2 (MulAut (LinearGroup 5)) ≤ 6 := by
  have hi : primeRank 2 (LinearGroup 5) ≤ 6 := by
    rw [← primeRank_equiv 2 (projectiveEquivLinear (by decide : 0 < 5))]
    exact Theory.SpecificGroups.PSL5Two.primeRank_le_six
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  have hr : primeRank 2 E ≤ 6 := by
    by_cases h : E ≤ MulAut.innerSubgroup (LinearGroup 5)
    · let f : E →* LinearGroup 5 :=
        fiveInnerEquiv.symm.toMonoidHom.comp (Subgroup.inclusion h)
      exact (primeRank_le_of_injective 2 f
        (fiveInnerEquiv.symm.injective.comp (Subgroup.inclusion_injective h))).trans hi
    · exact (five_outer_elementary_rank_le E h).trans (by decide)
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hc := (primeRank_le_iff_elementary_card_le E).mp hr ⊤ ht
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hc

/-- The intrinsic two-rank bound for the full automorphism group of PSL₅(2). -/
theorem psl5_two_rank_le :
    primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))) ≤ 6 := by
  rw [primeRank_equiv 2 (MulAut.congr (projectiveEquivLinear (by decide : 0 < 5)))]
  exact five_linear_automorphism_rank_le

/-- The inner six-dimensional elementary subgroup attains the automorphism bound. -/
theorem psl5_two_rank_eq :
    primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))) = 6 := by
  apply Nat.le_antisymm psl5_two_rank_le
  rw [primeRank_equiv 2 (MulAut.congr (projectiveEquivLinear (by decide : 0 < 5)))]
  have hi : 6 ≤ primeRank 2 (LinearGroup 5) := by
    rw [← primeRank_equiv 2 (projectiveEquivLinear (by decide : 0 < 5))]
    exact Theory.SpecificGroups.PSL5Two.six_le_primeRank
  exact hi.trans (primeRank_le_of_injective 2 MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot five_center_eq_bot))

end BinaryLinear.AutomorphismTwoRank

end
