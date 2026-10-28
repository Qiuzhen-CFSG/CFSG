module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingSylow

/-!
# Direct minimal escaping-plane selection

The actual ResidualInput gives the Sylow geometry needed to inherit
characteristic two on Mc ∩ I. Minimality in the genuine H-family then makes
this intersection maximal in an escaping I. These are precisely the selection
inputs for the ordinary component source route; no partner residual identity
or PlaneUniquenessPreceding record is used.

Source: Aschbacher--Smith 15.2.20 and the selection preceding 15.2.23,
printed pp.1113--1115, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r

/-- The literal offender plane is abelian and centralizes itself. -/
theorem ResidualInput.plane_le_centralizer_direct :
    ⁅V,B⁆ ≤ centralizer (⁅V,B⁆ : Subgroup G) := by
  let := h.prepared.elementary
  have hVV : V ≤ centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact r.geometry.plane_le.trans (hVV.trans (centralizer_le r.geometry.plane_le))

/-- Original 15.2.20(2) follows directly from the index-two inheritance theorem,
with normality and Sylow restriction taken inside Mc. -/
theorem ResidualInput.intersection_characteristicTwo_direct {I : Subgroup G} (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    generalizedFitting (Mc ⊓ I : Subgroup G) = pCore 2 (Mc ⊓ I : Subgroup G) := by
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      h.partner ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    exact r.geometry.outside.1.1.2.trans r.geometry.in_partner
  have hSMI : planeSylow T ⁅V,B⁆ ≤ Mc ⊓ I :=
    le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)
  have hne : Mc ⊓ I ≠ ⊥ := by
    intro he
    have hb : ⁅V,B⁆ = ⊥ := bot_unique ((r.plane_le_centralizer_direct.trans
      (r.plane_centralizer_le_intersection hI)).trans_eq he)
    have hc := r.geometry.plane_card
    rw [hb,Subgroup.card_bot] at hc
    omega
  have hi : ((Mc ⊓ I).subgroupOf Mc).relIndex ((T.subtype hTMc : Sylow 2 Mc) : Subgroup Mc) ≤ 2 := by
    change ((Mc ⊓ I).subgroupOf Mc).relIndex ((T : Subgroup G).subgroupOf Mc) ≤ 2
    rw [relIndex_subgroupOf hTMc]
    exact (relIndex_le_of_le_left hSMI index_ne_zero_of_finite).trans_eq (r.escape_index hI).2
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_7
      (Chapter1.mem_He_iff.mpr (h.ambient.evenCharacteristic T Mc hMc hTMc))
      (T.subtype hTMc) hne inf_le_left hi))

/-- Minimality applies to all intermediate subgroups containing MI: the actual
normal two-core of I is carried by S and survives in each such subgroup. -/
theorem ResidualInput.minimal_intermediate_direct {I J : Subgroup G} (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hMIJ : Mc ⊓ I ≤ J) (hJI : J ≤ I) : J = Mc ⊓ I ∨ J = I := by
  by_cases hJMc : J ≤ Mc
  · exact Or.inl (le_antisymm (le_inf hJMc hJI) hMIJ)
  · right
    apply le_antisymm hJI
    apply hI.2
    · have hcore : I.pCoreIn 2 ≤ planeSylow T ⁅V,B⁆ := by
        obtain ⟨P,hP⟩ := r.sylow_in_escape hI.1
        exact (pCoreIn_le_sylow I P).trans_eq hP
      have hQJ : I.pCoreIn 2 ≤ J := hcore.trans
        ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI.1)).trans hMIJ)
      have hQQ : I.pCoreIn 2 ≤ J.pCoreIn 2 := by
        simpa only [inf_eq_right.mpr hQJ] using inf_pCoreIn_le_of_le 2 hJI
      refine ⟨?_,?_,hJMc⟩
      · intro hbot
        exact hI.1.1 (bot_unique (hQQ.trans_eq hbot))
      · exact (le_inf inf_le_left hI.1.2.1).trans hMIJ
    · exact hJI

omit [Finite G] r in
/-- The strict intersection is the source maximal subgroup MI of the minimal I. -/
theorem minimal_intersection_lt_direct {I : Subgroup G} (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I) :
    Mc ⊓ I < I :=
  lt_of_le_of_ne inf_le_right (fun he => hI.1.2.2 (he ▸ inf_le_left))

/-- Failure of the requested singleton theorem produces a minimal genuine
H-overgroup. This is the selection made on printed p.1115. -/
theorem ResidualInput.exists_minimal_escape_direct
    (hne : maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V,B⁆ : Subgroup G)) ≠ {Mc}) :
    ∃ I : Subgroup G, MinimalPlaneEscape Mc ⁅V,B⁆ I := by
  classical
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      h.partner ▸ Set.mem_singleton Mc).1
  have hex : ∃ N ∈ maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V,B⁆ : Subgroup G)), N ≠ Mc := by
    by_contra! hn
    apply hne
    ext N
    constructor
    · exact fun hN => Set.mem_singleton_iff.mpr (hn N hN)
    · rintro rfl
      exact ⟨hMc,inf_le_left⟩
  obtain ⟨N,hN,hNM⟩ := hex
  have hescape : PlaneEscapes Mc ⁅V,B⁆ N := by
    refine ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2,?_⟩
    intro hle
    exact hNM (le_antisymm hle (hN.1.2 hMc.1 hle))
  exact (Set.toFinite {I | PlaneEscapes Mc ⁅V,B⁆ I}).exists_minimal ⟨N,hescape⟩


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
