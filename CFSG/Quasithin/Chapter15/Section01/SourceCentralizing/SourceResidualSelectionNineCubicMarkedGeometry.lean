module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePreExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableMarkedCore

/-!
# The original marked four-group in the strict Nine source

The marked centralizer has index two in the original Sylow subgroup. Its
marked line therefore cannot lie in the central seed. Inside the four-element
Thompson fixed subgroup, the nontrivial seed and the marked line are distinct
order-two subgroups and generate the whole fixed subgroup.

When the actual partner is the seed centralizer, this identifies the literal
M_Z with the centralizer of the fixed four-group. The same fixed subgroup
then lies in the central omega subgroup of the literal Q₁. These conclusions
use no residual-centralization or component reconstruction hypothesis.

Source: Aschbacher--Smith 15.1.13, 15.1.17--20, printed pp.1090,1093--1094.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem card_two_of_nontrivial_lt_four
    {U E : Subgroup G} (hU : U ≠ ⊥) (hUE : U < E) (hE : Nat.card E = 4) :
    Nat.card U = 2 := by
  have hlow := (one_lt_card_iff_ne_bot U).mpr hU
  have hle : Nat.card U ≤ 4 := (card_le_of_le hUE.le).trans_eq hE
  have hd : Nat.card U ∣ 4 := hE ▸ card_dvd_of_le hUE.le
  have hne4 : Nat.card U ≠ 4 := by
    intro he
    exact hUE.ne (eq_of_le_of_card_ge hUE.le (by rw [hE,he]))
  have hne3 : Nat.card U ≠ 3 := by
    intro he
    rw [he] at hd
    norm_num at hd
  omega

/-- The original index-two marking complements the central seed in a fixed
four-group, and identifies its marked centralizer and central radical. -/
theorem CaseIComponentData.marked_four_geometry_of_index_two
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V) (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hfour : Nat.card (thompsonFixed T V) = 4)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ1 : Nat.card d.Z1 = 2) (hindex : d.S.relIndex (T : Subgroup G) = 2) :
    Nat.card (centralInvolutions T) = 2 ∧
      Disjoint d.Z1 (centralInvolutions T) ∧
      d.Z1 ⊔ centralInvolutions T = thompsonFixed T V ∧
      d.MZ = centralizer (thompsonFixed T V : Set G) ∧
      thompsonFixed T V ≤ omegaOneCenterAmbient d.Q1 := by
  have hZE : centralInvolutions T ≤ thompsonFixed T V := by
    refine le_inf ?_ ?_
    · rw [hfull]
      exact le_conjugateSpanBy _ _
    · intro z hz j hj
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j
        (ChapterB.thompsonJ_le _ _ hj)
  have hZne := centralInvolutions_ne_bot_of_maximal_local T hM.1
  have hnot : ¬ d.Z1 ≤ centralInvolutions T := by
    intro hz
    have hTS : (T : Subgroup G) ≤ d.S := le_inf le_rfl
      ((le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
        (centralizer_le hz))
    have hi := relIndex_eq_one.mpr hTS
    rw [hindex] at hi
    norm_num at hi
  have hZElt : centralInvolutions T < thompsonFixed T V :=
    lt_of_le_of_ne hZE (fun he => hnot (d.Z1_le_fixed.trans_eq he.symm))
  have hZtwo := card_two_of_nontrivial_lt_four hZne hZElt hfour
  have hdisj : Disjoint d.Z1 (centralInvolutions T) := by
    apply disjoint_iff.mpr
    by_contra hn
    have hlow := (one_lt_card_iff_ne_bot (d.Z1 ⊓ centralInvolutions T)).mpr hn
    have he : d.Z1 ⊓ centralInvolutions T = d.Z1 :=
      eq_of_le_of_card_ge inf_le_left (by rw [hZ1]; omega)
    exact hnot (he ▸ (inf_le_right : d.Z1 ⊓ centralInvolutions T ≤ centralInvolutions T))
  have hgen : d.Z1 ⊔ centralInvolutions T = thompsonFixed T V := by
    have hle : d.Z1 ⊔ centralInvolutions T ≤ thompsonFixed T V :=
      sup_le d.Z1_le_fixed hZE
    by_contra hn
    have hne : d.Z1 ⊔ centralInvolutions T ≠ ⊥ := by
      intro he
      exact hZne (bot_unique ((le_sup_right : centralInvolutions T ≤
        d.Z1 ⊔ centralInvolutions T).trans_eq he))
    have htwo := card_two_of_nontrivial_lt_four hne (lt_of_le_of_ne hle hn) hfour
    have he : centralInvolutions T = d.Z1 ⊔ centralInvolutions T :=
      eq_of_le_of_card_ge le_sup_right (by rw [hZtwo,htwo])
    exact hnot (he.symm ▸ (le_sup_left : d.Z1 ≤ d.Z1 ⊔ centralInvolutions T))
  have hMZ : d.MZ = centralizer (thompsonFixed T V : Set G) := by
    change centralizer (d.Z1 : Set G) ⊓ Mc = _
    apply le_antisymm
    · apply le_centralizer_iff.mpr
      rw [←hgen]
      exact sup_le (le_centralizer_iff.mp inf_le_left)
        (le_centralizer_iff.mp (inf_le_right.trans hMc.le))
    · exact le_inf (centralizer_le d.Z1_le_fixed) ((centralizer_le hZE).trans_eq hMc.symm)
  let := h.elementary
  let : IsElementaryAbelian 2 (thompsonFixed T V) := IsElementaryAbelian.of_le inf_le_left
  exact ⟨hZtwo,hdisj,hgen,hMZ,d.le_omegaCenter_radical_of_marked_centralizer _ hMZ⟩

/-- The literal strict-image Nine source has complementary original lines
and its fixed four-group lies in Ω₁Z(Q₁), on the same selected component. -/
theorem PreparedChosenModule.nine_marked_core_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)
    (d : CaseIComponentData T M Mc V) (hr : d.row = .four)
    (g : d.ExchangedPlaneGeometry) :
    Nat.card (centralInvolutions T) = 2 ∧
      Disjoint d.Z1 (centralInvolutions T) ∧
      d.Z1 ⊔ centralInvolutions T = thompsonFixed T V ∧
      d.MZ = centralizer (thompsonFixed T V : Set G) ∧
      thompsonFixed T V ≤ omegaOneCenterAmbient d.Q1 := by
  have hfour := (h.nine_fixed_card_of_strict_thompson_image
    hG T hempty hM hmany hJ h9 hstrict).2
  have hMc := (h.nine_partner_centralizer hG T hempty hM hJ hu hne hfull h9).1
  have hZ1 : Nat.card d.Z1 = 2 := by
    rcases g.sizes with hs | hs
    · exact hs.2.1
    · cases hr.symm.trans hs.1
  exact d.marked_four_geometry_of_index_two hM h hfull hfour hMc hZ1 g.index

end CFSG.Quasithin.Chapter15.Section01
