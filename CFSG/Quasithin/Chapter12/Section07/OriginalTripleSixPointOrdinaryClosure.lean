module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPushingUpAt
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement

/-!
# The literal ordinary closure at the original triple-six point

Every ordinary component of H contains the original Lt. Normality puts its
whole H-closure in that component. Conversely the component either lies in
this normal closure or centralizes it. The latter would centralize the
original U, contrary to the genuine C.2.8 module placement. Thus the selected
ordinary component is exactly the original closure, and the original point
lies in its two-group center.

This is the ordinary placement step in 12.7.5, before identification of the
central quotient as PSL3(4). Source: Aschbacher--Smith, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- An ordinary component is the literal H-conjugate closure of the
original point residual, not an abstract replacement of that subgroup. -/
theorem original_tripleSix_point_ordinary_closure_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    B = J.map H.subtype ∧ IsComponent H (B.subgroupOf H) ∧
      (t : G) ∈ centerIn B ∧ centerIn B = B.pCoreIn 2 := by
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G) ⊓ H
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let A := B.subgroupOf H
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hLH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hBH : B ≤ H := conjugateSpanBy_le_self hLH
  have hLJ : Lt ≤ J.map H.subtype := by
    have hm := map_mono (f := H.subtype) (h28.ordinary_component_contains_original J hJ)
    rwa [map_subgroupOf_eq_of_le hLH] at hm
  let : J.Normal := h28.ordinary_component_normal J hJ
  have hHJ : H ≤ normalizer (J.map H.subtype : Set G) := by
    intro x hx
    exact J.le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype (show (⟨x,hx⟩ : H) ∈ normalizer (J : Set H) by
        rw [normalizer_eq_top]; trivial))
  have hBJ : B ≤ J.map H.subtype := conjugateSpanBy_le hLJ hHJ
  have hAJ : A ≤ J := by
    intro x hx
    exact (mem_map_iff_mem H.subtype_injective).mp (hBJ hx)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hBH).mpr
    (le_normalizer_conjugateSpanBy Lt H)
  have hJA : J ≤ A := by
    rcases hJ.normal_dichotomy A with hle | hc
    · exact hle
    exfalso
    have hUA : U.subgroupOf H ≤ A :=
      comap_mono ((tripleSixPointCentralizerResidual_commutator D a t ht heven).2.trans
        (le_conjugateSpanBy Lt H))
    exact (h28.ordinary_module_placement J hJ).2
      (hUA.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))
  have hAJ' : A = J := le_antisymm hAJ hJA
  have hB : B = J.map H.subtype := by
    have hm := congrArg (map H.subtype) hAJ'
    simpa only [A,map_subgroupOf_eq_of_le hBH] using hm
  have hcomponent : IsComponent H A := hAJ'.symm ▸ hJ
  have htB : (t : G) ∈ B := (le_conjugateSpanBy Lt H)
    ((tripleSixPointCentralizerResidual_commutator D a t ht heven).2 t.property)
  have htZ : (t : G) ∈ centerIn B := by
    rw [centerIn_eq_map_center]
    exact ⟨⟨t,htB⟩,mem_center_iff.mpr (fun x => Subtype.ext
      (mem_centralizer_singleton_iff.mp (hBH x.property))),rfl⟩
  have hcenter : centerIn B = B.pCoreIn 2 := by
    let : IsQuasisimple A := hcomponent.2
    let e : A ≃* B := subgroupOfEquivOfLe hBH
    let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
    have hodd : pPrimeCore 2 B = ⊥ := by
      have hm := pPrimeCore_map_iso 2 e
      rw [hcomponent.1.pPrimeCore_eq_bot h28.oddCore_eq_bot A,Subgroup.map_bot] at hm
      exact hm.symm
    rw [centerIn_eq_map_center]
    exact congrArg (map B.subtype) (IsQuasisimple.center_eq_pCore hodd)
  exact ⟨hB,hcomponent,htZ,hcenter⟩

end CFSG.Quasithin.Chapter12.Section07
