module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Source
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ReducedSolvability
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.RankOneFieldSize
/-!
# The original paired natural field is larger than two

If the common field were binary of degree one, the actual offender product
would be solvable. Its two-group quotient and the original reduced action
kernel then make the original minimal parabolic solvable. Thus the genuine
nonsolvable branch has two perfect SL₂ factors.

Source: Aschbacher–Smith B.6.9 and C.1.26, printed pp.115–116 and132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem paired_linear_field_large
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    2 < Nat.card F.Carrier := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let := offenderSubgroup_normal α
  by_contra hn
  have hd : F.degree = 1 := by
    have hdpos := F.degree_pos
    have hn' : 2^F.degree ≤ 2 := by simpa only [F.card_eq] using Nat.le_of_not_gt hn
    by_contra h
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    norm_num at hpow
    omega
  let e := (ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype,←alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective
    (f := c.action.groupEquiv.symm.toMonoidHom) c.action.groupEquiv.symm.surjective
  have hcore : pCore 2 H = ⊥ := by
    let eq := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 eq,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hqne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hqne).2
  have hff : IsFFModule α := by
    obtain hh | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hh.1)).elim
    · exact hf
  have hr : pResidual 2 H ≤ Y := (offender_generation (T.mapSurjective hq) hp α hff hcore).1
  let : Group.IsSolvable (pResidual 2 H) := Group.isSolvable_of_isSolvable_injective (inclusion_injective hr)
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hh : Group.IsSolvable H := (Group.isSolvable_iff_subgroup_quotient (pResidual 2 H)).mpr
    ⟨inferInstance,inferInstance⟩
  exact hs (solvable_of_reduced_minimalParabolic_action T hP U hU hJ q hq hk hh)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
