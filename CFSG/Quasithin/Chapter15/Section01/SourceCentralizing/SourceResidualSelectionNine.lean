module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMaximal
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonGeneration
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual.ProperImageTwo.FixedPlane

/-!
# Original maximal-overgroup geometry of the full Nine action

The literal Nine Sylow image is maximal in the full action. The actual
third-maximal action constraints therefore exclude every third maximal
local. The same image maximality forces the original partner intersection
onto precisely that Sylow image and identifies the partner with C_G(Z).
In the strict Thompson-image branch, source movement and the order-four
Sylow image give an order-two Thompson image and a four-element fixed group.

These statements retain the original prepared full module. They do not
promote the pair of maximal overgroups, or the local fixed-plane size, to
the global normalization in original 15.1.14.

Source: Aschbacher--Smith 15.1.2(5), 15.1.13--14 and the actual intersection
argument of 15.2.5, printed pp.1086,1090--1091,1107--1108.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The genuine Nine action admits no third maximal two-local over the
original Sylow subgroup. No residual conclusion is an input. -/
theorem PreparedChosenModule.nine_maximal_overgroups
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : PreparedChosenModule T M V)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict)) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  classical
  let := hp.elementary
  let D := internalActionImage M V hp.normalized
  let f : M →* D := (actionHom M V hp.normalized).rangeRestrict
  let P := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V hp.normalized).rangeRestrict_surjective
  have hmax := h9.sylow_isCoatom P
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N=M
    · simp [hNM]
    by_cases hNMc : N=Mc
    · simp [hNMc]
    obtain ⟨_,hnot,hproper⟩ := hp.third_maximal_action_constraints
      hG T hempty hM hJ hu hN hNM hNMc
    let A := ((M ⊓ N).subgroupOf M).map f
    have hPA : (P : Subgroup D) < A := by
      refine lt_of_le_of_ne (map_mono
        (subgroupOf_mono M (le_inf hM.1.2 hN.2))) ?_
      intro he
      exact hnot (show IsPGroup 2 A by rw [←he]; exact P.isPGroup')
    exact (hproper (hmax.2 A hPA)).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

/-- In the strict Thompson-image branch of the genuine Nine action, the
actual image has order two and the original fixed subgroup has order four. -/
theorem PreparedChosenModule.nine_fixed_card_of_strict_thompson_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hp : PreparedChosenModule T M V)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hp.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict) :
    Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hp.normalized).rangeRestrict)=2 ∧
      Nat.card (thompsonFixed T V)=4 := by
  let := hp.elementary
  let f := (actionHom M V hp.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let S := ((T : Subgroup G).subgroupOf M).map f
  obtain ⟨_,_,hdim,_,_,_,hS,_⟩ := h9
  have hm := (hp.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hne : J≠⊥ := chosen_thompson_image_ne_bot _ _ _ hM.1.2 hp.normalized hm
  have hlo := (one_lt_card_iff_ne_bot J).mpr hne
  have hle : Nat.card J ≤ 4 := (card_le_of_le hstrict.le).trans_eq hS.2
  have hdiv : Nat.card J ∣ 4 := hS.2 ▸ card_dvd_of_le hstrict.le
  have hne4 : Nat.card J≠4 := by
    intro he
    exact hstrict.ne (eq_of_le_of_card_ge hstrict.le (hS.2.le.trans he.ge))
  have hne3 : Nat.card J≠3 := by
    intro he
    rw [he] at hdiv
    norm_num at hdiv
  have ht : Nat.card J=2 := by omega
  exact ⟨ht,hp.thompsonFixed_card_of_image_two T hM.1.2 hdim ht⟩

end CFSG.Quasithin.Chapter15.Section01
