module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Graph

/-!
# The degree-two row forces even outer degree on its full-normalizer extension

The marked degree-two comparison supplies an actual graph involution in the
original whole overlap. The constructed full-normalizer marking carries that
same involution to an order-two element outside the inner automorphism group.
Thus its outer index is even. This records the degree-two row as an explicit
obstruction to the odd-degree conclusion, without discarding its kernel or
changing the chosen extension.

Source: Aschbacher--Smith F.4.37--38, pp.293--294, and 5.3.2, p.659 of
`refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

private theorem two_subgroup_le_of_odd_index
    {X : Type*} [Group X] [Finite X] (N P : Subgroup X) [N.Normal]
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ N.index) : P ≤ N := by
  have hi : N.relIndex P = 1 := by
    obtain ⟨k,hk⟩ := hP.index (N.subgroupOf P)
    have hn : ¬ 2 ∣ 2^k := fun hd => hodd
      ((hk ▸ hd).trans (N.relIndex_dvd_index_of_normal P))
    have hk0 : k = 0 := by
      by_contra hh
      exact hn (dvd_pow_self 2 hh)
    change (N.subgroupOf P).index = 1
    rw [hk,hk0,pow_zero]
  exact (relIndex_eq_one.mp hi)

private theorem involution_cyclic_two_group {X : Type*} [Group X] [Finite X]
    (x : X) (hx : orderOf x = 2) : IsPGroup 2 (zpowers x) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Nat.card_zpowers]
  have hxpow := pow_orderOf_eq_one x
  rw [hx] at hxpow
  exact orderOf_dvd_of_pow_eq_one hxpow

/-- The genuine degree-two comparison forces even index of the inner group
in the same prepared full-normalizer extension. Both endpoint orientations
are retained. -/
theorem Preparation.unitaryFour_degreeTwo_outer_index_even
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    2 ∣ (inner (ProjectiveGroup m hm)).relIndex
      (d.unitaryFourNormalizerMarking h hH hp m hm (Or.inr hc)).extension.carrier := by
  obtain ⟨_,_,g,_,_,_,_,_,hg,hmarked⟩ :=
    d.unitaryFour_constructed_graph h hH hp m hm hc
  rcases hmarked with
    ⟨_,_,F,_,_,_,horder,houter⟩ | ⟨_,_,F,_,_,_,horder,houter⟩
  all_goals
    let E := (d.unitaryFourNormalizerMarking h hH hp m hm (Or.inr hc)).extension
    let xMiddle := F.middle ⟨g,hg⟩
    let x : E.carrier := inclusion (inf_le_left.trans E.left_le) xMiddle
    have hx : orderOf x = 2 :=
      (orderOf_injective (inclusion (inf_le_left.trans E.left_le))
        (inclusion_injective (inf_le_left.trans E.left_le)) xMiddle).trans horder
    letI : (ChapterF.SourceCompletion.UnitaryNonbinary.inner
      (ProjectiveGroup m hm)).Normal := by
      constructor
      rintro _ ⟨b,rfl⟩ a
      refine ⟨a b,?_⟩
      ext y
      simp [MulAut.conj_apply,map_mul]
    let I := (ChapterF.SourceCompletion.UnitaryNonbinary.inner
      (ProjectiveGroup m hm)).subgroupOf E.carrier
    letI : I.Normal := inferInstance
    by_contra hodd
    have hI : ¬ 2 ∣ I.index := by
      change ¬ 2 ∣ (ChapterF.SourceCompletion.UnitaryNonbinary.inner
        (ProjectiveGroup m hm)).relIndex E.carrier
      exact hodd
    have hP := involution_cyclic_two_group x hx
    have hle := two_subgroup_le_of_odd_index I (zpowers x) hP hI
    have hxin : x ∈ I := hle (mem_zpowers x)
    have hinner : x.val ∈ ChapterF.SourceCompletion.UnitaryNonbinary.inner
        (ProjectiveGroup m hm) := hxin
    exact houter (by simpa [x,xMiddle,E] using hinner)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
