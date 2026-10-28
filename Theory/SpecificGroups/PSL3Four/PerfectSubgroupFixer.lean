module
public import Theory.SpecificGroups.PSL3Four.InnerInvolutionCentralizers
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.Quasithin.Rank
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Perfect subgroup fixers in PSL₃(4)

A square-one automorphism of PSL₃(4) that fixes a perfect subgroup of two-rank
at least three is trivial. An outer involution has fixed-group two-rank at
most two. For an inner involution, the inner centralizer is a 2-group;
a nontrivial perfect group cannot embed in it. Faithfulness of the quotient
action then gives the same assertion for every perfect central cover.

The literal image of the subgroup is retained in the cover theorem. This
supplies the linear containing-component rows in Aschbacher–Smith, proof of
10.2.9, pp.750–751 (1 March 2004 manuscript), without identifying an arbitrary
perfect cover with SL₃(4).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3Four.PerfectSubgroupFixer

/-- An involutory automorphism fixing a perfect subgroup of two-rank above two is trivial. -/
theorem eq_one_of_fixes_perfect_high_rank (a : MulAut PSL) (hsq : a ^ 2 = 1)
    (B : Subgroup PSL) [Group.IsPerfect B] (hr : 2 < primeRank 2 B)
    (hfix : B ≤ a.fixedSubgroup) : a = 1 := by
  by_contra hne
  by_cases hi : a ∈ MulAut.innerSubgroup PSL
  · have hinj : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
      let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
      exact MulAut.conj_injective_of_center_eq_bot
        (Group.IsPerfect.center_quotient_center_eq_bot SL)
    let j : B →* InnerInvolutionCentralizers.innerCentralizer a :=
      (MulAut.conj.comp B.subtype).codRestrict _ (fun b => ⟨⟨b, rfl⟩, by
        apply mem_centralizer_singleton_iff.mpr
        have hb := (MulAut.mem_fixedSubgroup a b).mp (hfix b.property)
        ext x
        change (b : PSL) * a x * (b : PSL)⁻¹ = a ((b : PSL) * x * (b : PSL)⁻¹)
        rw [map_mul,map_mul,map_inv,hb]⟩)
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      exact hinj (congrArg Subtype.val h)
    have hp : IsPGroup 2 B :=
      (InnerInvolutionCentralizers.innerCentralizer_isTwoGroup a hi hne hsq).of_injective j hj
    have ht : Nontrivial B := by
      by_contra h
      have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
      have hh : primeRank 2 B ≤ 1 := by
        simpa [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] using (primeRank_le_nat_card (G := B) 2)
      omega
    let := ht
    exact Group.IsPerfect.not_isNilpotent B hp.isNilpotent
  · have hb := Matrix.PSL3Even.OuterElementaryRank.FixedRanks.outer_involution_fixed_rank_le
      (F := F) (f := 2) (by decide) (by simpa using card_F) a
      (by rw [Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F
        (m := 2) (by decide) (by simpa using card_F)]; trivial) hsq hi
    have hh := (primeRank_mono 2 hfix).trans hb
    omega
end Matrix.PSL3Four.PerfectSubgroupFixer

namespace Matrix.PSL3Four.PerfectSubgroupFixer
/-- Faithful descent through a perfect central cover retains the actual image. -/
theorem centralCover_eq_one_of_fixes_perfect_high_rank
    {K : Type*} [Group K] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* PSL) (a : MulAut K) (hsq : a ^ 2 = 1)
    (B : Subgroup K) [Group.IsPerfect B]
    (hr : 2 < primeRank 2 (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))))
    (hfix : B ≤ a.fixedSubgroup) : a = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let C := B.map q
  let : Group.IsPerfect C := Group.IsPerfect.map q
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply eq_one_of_fixes_perfect_high_rank _ (by rw [←map_pow,hsq,map_one]) C hr
  rintro x ⟨b,hb,rfl⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [show q b = e (QuotientGroup.mk' (center K) b) from rfl,
    MulAut.centralQuotientAction_apply, (MulAut.mem_fixedSubgroup a b).mp (hfix hb)]
end Matrix.PSL3Four.PerfectSubgroupFixer
