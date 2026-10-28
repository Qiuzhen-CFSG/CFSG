module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual.ProperImageTwo.CoreContainment
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNine
public import Theory.GroupTheory.CyclicSubgroupNormalizer

/-!
# The actual moving parabolic core in the original Nine row

The Thompson image is the unique involution subgroup of the cyclic action
Sylow of order four. Any subgroup of T which moves its fixed subgroup must
therefore induce the entire cyclic Sylow action. For the parabolic selected
by a failure of original 15.1.14, the characteristic-two four-group argument
puts the fixed subgroup in the same parabolic core, and its noncentrality
forces this full action image.

The selected parabolic, original module, and action map remain unchanged.
This is a necessary obstruction for the remaining residual argument.
Source: Aschbacher--Smith 15.1.7(4), 15.1.13--14, printed pp.1087,1090--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem le_two_of_lt_cyclic_four
    {D : Type*} [Group D] [Finite D] (S R A : Subgroup D) [IsCyclic S]
    (hS : Nat.card S = 4) (hR : Nat.card R = 2) (hRS : R ≤ S) (hAS : A < S) :
    A ≤ R := by
  have hd : Nat.card A ∣ 2 ^ 2 := by simpa [hS] using card_dvd_of_le hAS.le
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · have hA : A = ⊥ := (eq_bot_iff_card A).mpr (by simpa using he)
    exact hA ▸ bot_le
  · have hA : Nat.card A = 2 := by simpa using he
    intro a ha
    have ha2 : a ^ 2 = 1 := by
      have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))
      change a ^ Nat.card A = 1 at hh
      rwa [hA] at hh
    have hp : (⟨a,hAS.le ha⟩ : S) ^ Nat.card (R.subgroupOf S) = 1 := by
      apply Subtype.ext
      rw [Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv,hR]
      exact ha2
    exact mem_of_pow_card_eq_one_in_cyclic (R.subgroupOf S) hp
  · exact (hAS.ne (eq_of_le_of_card_ge hAS.le (by rw [hS,he]; norm_num))).elim

/-- A subgroup of the original Sylow group moving the Thompson fixed plane
has the full cyclic-four action image. -/
theorem PreparedChosenModule.image_eq_sylow_of_cyclic_four_fixed_movement
    (T : Sylow 2 G) {M V Q : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V)
    (hcyc : IsCyclic (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict))
    (hfour : Nat.card (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) = 4)
    (htwo : Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) = 2)
    (hQT : Q ≤ (T : Subgroup G))
    (hmove : ¬ Q ≤ centralizer (thompsonFixed T V : Set G)) :
    (Q.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  let f := (actionHom M V h.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let A := (Q.subgroupOf M).map f
  let : IsCyclic S := hcyc
  have hAS : A ≤ S := map_mono (subgroupOf_mono M hQT)
  have hRS : R ≤ S := map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))
  change A = S
  by_contra hne
  have hAR : A ≤ R := le_two_of_lt_cyclic_four S R A hfour htwo hRS
    (lt_of_le_of_ne hAS hne)
  apply hmove
  intro q hq v hv
  let qM : M := ⟨q,hTM (hQT hq)⟩
  have hqR : f qM ∈ R := hAR (mem_map_of_mem f hq)
  obtain ⟨j,hj,he⟩ := hqR
  have heval := congrArg (fun a : internalActionImage M V h.normalized =>
    ((a.val ⟨v,hv.1⟩ : V) : G)) he
  change (j : G) * v * (j : G)⁻¹ = q * v * q⁻¹ at heval
  have hjv : (j : G) * v = v * (j : G) := hv.2 j hj
  have hqv : q * v * q⁻¹ = v := by
    rw [←heval,hjv,mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp hqv).symm

/-- The same selected moving parabolic has its fixed plane in its two-core,
and that core induces the entire cyclic-four action of the Nine row. -/
theorem PreparedChosenModule.nine_moving_parabolic_core_image_of_fixed_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (htwo : Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) = 2)
    (hfour : Nat.card (thompsonFixed T V) = 4)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ P : Subgroup G, P ≤ centralizer (centralInvolutions T : Set G) ∧
      P ∈ Chapter1.HOver G (T : Set G) ∧ ChapterB.IsMinimalParabolicOver T P ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ generalizedFitting P = pCore 2 P ∧
      ¬ P ≤ M ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G) ∧
      thompsonFixed T V ≤ P.pCoreIn 2 ∧
      ¬ P.pCoreIn 2 ≤ centralizer (thompsonFixed T V : Set G) ∧
      ((P.pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  let := h.elementary
  obtain ⟨P,hPC,hPH,hP,hSQ,hF,hPM,hmove,_⟩ :=
    h.thompsonFixed_moving_minimalParabolic hG T hM hJ hnot
  have hEQ := h.thompsonFixed_four_le_core hG T hM hfour hPH hPC
  have hQmove := h.moving_fixed_four_core_not_centralizes
    hG T hempty hM hJ hfour hPH hPC hP hPM hmove
  have hQT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hle := pCoreIn_le_sylow P (T.subtype hPH.2)
    change P.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P).map P.subtype at hle
    rwa [map_subgroupOf_eq_of_le hPH.2] at hle
  obtain ⟨_,_,_,_,_,_,hS,_⟩ := h9
  exact ⟨P,hPC,hPH,hP,hSQ,hF,hPM,hmove,hEQ,hQmove,
    h.image_eq_sylow_of_cyclic_four_fixed_movement T hM.1.2 hS.1 hS.2 htwo hQT hQmove⟩

/-- A failure in the genuine strict-image Nine row has a moving parabolic
whose core contains the original fixed plane and induces the full C4 action.
The image and fixed-plane orders are derived from the original source inputs. -/
theorem PreparedChosenModule.nine_moving_parabolic_core_image
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
      ¬ P.pCoreIn 2 ≤ centralizer (thompsonFixed T V : Set G) ∧
      ((P.pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  obtain ⟨htwo,hfour⟩ := h.nine_fixed_card_of_strict_thompson_image
    hG T hempty hM hmany hJ h9 hstrict
  exact h.nine_moving_parabolic_core_image_of_fixed_card hG T hempty hM hJ h9 htwo hfour hnot

end CFSG.Quasithin.Chapter15.Section01
