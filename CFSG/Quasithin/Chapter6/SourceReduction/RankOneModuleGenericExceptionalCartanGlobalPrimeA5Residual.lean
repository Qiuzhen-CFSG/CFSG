module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCommonContainer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# The selected prime-source factor over an actual A5 residual

The literal two-residual is a C-component when its two-core quotient is A5.
Any selected H-component inside it is therefore equal to it. In the other
source branch the residual radical quotient has two-rank at least four.
The original A5 quotient identifies that radical quotient with a quotient
of A5, whose order divides sixty and whose two-rank is at most two.

Only containment and the retained source alternatives are used. No equality
of generation parameters, normalization, or completion model is assumed.
Source: Aschbacher--Smith A.3.3, E.2.2 and 5.2.2,
printed pp.42--43,215--216,646--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G] {H R : Subgroup G}

private theorem residual_radical_two_rank_le_two
    (e : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5)) :
    primeRank 2 ((residual H) ⧸ solvableRadical (residual H)) ≤ 2 := by
  let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 (pResidual 2 H))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let a : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let b := QuotientGroup.congr _ _ a (map_solvableRadical_equiv a)
  let c := b.symm.trans ((solvableRadicalQuotientEquiv q
    (QuotientGroup.mk'_surjective _)).trans
      (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)))
  rw [primeRank_equiv 2 c]
  apply primeRank_le_two_of_cube_not_dvd
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hdiv : Nat.card (alternatingGroup (Fin 5) ⧸
      solvableRadical (alternatingGroup (Fin 5))) ∣ 60 := by
    rw [←Subgroup.index_eq_card]
    exact hcard ▸ (solvableRadical (alternatingGroup (Fin 5))).index_dvd_card
  intro hc
  exact (by decide : ¬ 2^3 ∣ 60) (hc.trans hdiv)

/-- The retained actual source choice equals the whole residual whenever
the original intrinsic two-core quotient is A5. -/
theorem SelectedSourceModels.right_eq_residual_of_a5
    (hs : SelectedSourceModels H R) (hR : R ≤ residual H)
    (e : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5)) : R = residual H := by
  by_cases hC : (R.subgroupOf H).IsCComponent
  · let : IsQuasisimple (alternatingGroup (Fin 5)) := {
      toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      simple := by
        let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
          alternatingGroup.isSimpleGroup (by simp)
        exact ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
      IsQuasisimple.of_mulEquiv e.symm
    have hK : (pResidual 2 H).IsCComponent :=
      isCComponent_of_isPPerfect_of_quasisimple_core_quotient
        (inferInstance : (pResidual 2 H).Normal).isSubnormal (isPPerfect_pResidual 2)
    have hk : (residual H).subgroupOf H = pResidual 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    have hK' : ((residual H).subgroupOf H).IsCComponent := by
      rw [hk]
      exact hK
    have he : R.subgroupOf H = (residual H).subgroupOf H :=
      hC.eq_of_le hK' (comap_mono hR)
    have he' := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le (hR.trans (map_subtype_le _)),
      map_subgroupOf_eq_of_le (map_subtype_le (pResidual 2 H))] at he'
    exact he'
  · have hlo := hs.original_residual_radical_two_rank hC
    have hhi := residual_radical_two_rank_le_two e
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
