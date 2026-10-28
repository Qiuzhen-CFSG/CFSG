module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMovingCore
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# The moving core's action on the original Thompson fixed plane

The original fixed plane is normalized by T. Once it lies in a two-subgroup
Q of T and Q moves it, its centralizer has index two in Q: conjugation on a
normal elementary four-group has two-group image of order at most two.
Thus the same selected Nine parabolic has full cyclic-four action on V and
order-two action on the original fixed plane. No normality in the whole
parabolic is assumed.

Source: Aschbacher--Smith 15.1.13--14, printed pp.1090--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- A two-subgroup moving the original fixed four-group has centralizer
index two and literal conjugation image of order two on that fixed group. -/
theorem PreparedChosenModule.fixed_four_noncentral_action
    (T : Sylow 2 G) {M V Q : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V) (hfour : Nat.card (thompsonFixed T V) = 4)
    (hQT : Q ≤ (T : Subgroup G)) (hEQ : thompsonFixed T V ≤ Q)
    (hmove : ¬ Q ≤ centralizer (thompsonFixed T V : Set G)) :
    ∃ hn : Q ≤ normalizer (thompsonFixed T V : Set G),
      (centralizer (thompsonFixed T V : Set G)).relIndex Q = 2 ∧
      Nat.card (internalActionImage Q (thompsonFixed T V) hn) = 2 := by
  let := h.elementary
  let E := thompsonFixed T V
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hTM.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hn : Q ≤ normalizer (E : Set G) := hQT.trans hTN
  let U := E.subgroupOf Q
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEQ
  have hU : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans hfour
  have hC : centralizer (U : Set Q) = (centralizer (E : Set G)).subgroupOf Q := by
    ext q
    constructor
    · intro hq e he
      exact congrArg Q.subtype (hq (⟨e,hEQ he⟩ : Q) he)
    · intro hq u hu
      exact Subtype.ext (hq u hu)
  have hi : (centralizer (E : Set G)).relIndex Q = 2 := by
    have hb := centralizer_index_le_two_of_normal_four (T.isPGroup'.to_le hQT) U hU
    rw [hC] at hb
    have hz := ((centralizer (E : Set G)).subgroupOf Q).index_ne_zero_of_finite
    have hne : (centralizer (E : Set G)).relIndex Q ≠ 1 := by
      intro he
      exact hmove (relIndex_eq_one.mp he)
    change ((centralizer (E : Set G)).subgroupOf Q).index ≠ 1 at hne
    change ((centralizer (E : Set G)).subgroupOf Q).index = 2
    omega
  refine ⟨hn,hi,?_⟩
  change Nat.card (actionHom Q E hn).range = 2
  rw [← index_ker,actionHom_ker]
  exact hi

/-- The selected moving Nine parabolic has order-two action on its original
fixed plane, while its two-core retains the entire cyclic-four action on V. -/
theorem PreparedChosenModule.nine_moving_parabolic_fixed_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ P : Subgroup G, P ≤ centralizer (centralInvolutions T : Set G) ∧
      P ∈ Chapter1.HOver G (T : Set G) ∧ ChapterB.IsMinimalParabolicOver T P ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ generalizedFitting P = pCore 2 P ∧
      ¬ P ≤ M ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G) ∧
      thompsonFixed T V ≤ P.pCoreIn 2 ∧
      ((P.pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ∧
      ∃ hn : P.pCoreIn 2 ≤ normalizer (thompsonFixed T V : Set G),
        (centralizer (thompsonFixed T V : Set G)).relIndex (P.pCoreIn 2) = 2 ∧
        Nat.card (internalActionImage (P.pCoreIn 2) (thompsonFixed T V) hn) = 2 := by
  obtain ⟨P,hPC,hPH,hP,hSQ,hF,hPM,hmove,hEQ,hQmove,himage⟩ :=
    h.nine_moving_parabolic_core_image hG T hempty hM hmany hJ h9 hstrict hnot
  have hfour := (h.nine_fixed_card_of_strict_thompson_image
    hG T hempty hM hmany hJ h9 hstrict).2
  have hQT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hle := pCoreIn_le_sylow P (T.subtype hPH.2)
    change P.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P).map P.subtype at hle
    rwa [map_subgroupOf_eq_of_le hPH.2] at hle
  exact ⟨P,hPC,hPH,hP,hSQ,hF,hPM,hmove,hEQ,himage,
    h.fixed_four_noncentral_action T hM.1.2 hfour hQT hEQ hQmove⟩

end CFSG.Quasithin.Chapter15.Section01
