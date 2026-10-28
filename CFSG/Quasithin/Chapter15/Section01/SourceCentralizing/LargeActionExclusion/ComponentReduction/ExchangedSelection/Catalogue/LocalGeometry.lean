module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The two proper local intersections in original 15.1.22

The singleton centralizer overgroup puts T inside M_c. The actual M_Z
has characteristic two, so its intersection with the subnormal component
L has characteristic two as well. This argument applies to constrained
components as well as ordinary components. Both intersections contain the
same S_L and are proper in L, and C_L(Z) lies in M_L.

These are the common local hypotheses for the parabolic arguments in
15.1.20--22, not a parabolic classification. Source: Aschbacher--Smith,
printed pp.1094--1099, using 1.1.3 and 1.1.5.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- All selected components have the same characteristic-two local
intersection, without assuming that the whole centralizer G₁ has
characteristic two. -/
theorem PreExclusionSource.local_intersections
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hTM : (T : Subgroup G) ≤ M) :
    HasCharacteristicTwo d.ML ∧ d.SL ≤ d.ML ∧ d.ML < d.L ∧
      d.SL ≤ M ⊓ d.L ∧ M ⊓ d.L < d.L ∧
      d.L ⊓ centralizer (centralInvolutions T : Set G) ≤ d.ML := by
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hZT : d.Z1 ≤ (T : Subgroup G) :=
    (d.Z1_le_fixed.trans inf_le_left).trans hVT
  let : IsElementaryAbelian 2 d.Z1 :=
    IsElementaryAbelian.of_le (d.Z1_le_fixed.trans inf_le_left)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMZ : HasCharacteristicTwo d.MZ := Chapter1.mem_He_iff.mp
    (CaseIMarkedSubgroup.partner_centralizer_characteristic_two hG hu
      (IsElementaryAbelian.isPGroup 2 d.Z1) hZT)
  let A := d.L.subgroupOf d.G1
  let B := d.MZ.subgroupOf d.G1
  let eB : B ≃* d.MZ := subgroupOfEquivOfLe (show d.MZ ≤ d.G1 from inf_le_left)
  have hB : HasCharacteristicTwo B := hMZ.of_equiv eB.symm
  have hAB : HasCharacteristicTwo (A.subgroupOf B) :=
    subnormal_core_selfCentralizing hB (A.subgroupOf B)
      d.L_component.2.subnormal.subgroupOf
  let e : A.subgroupOf B ≃* d.ML := {
    toFun x := ⟨x.val.val, x.val.property, x.property⟩
    invFun x := ⟨⟨⟨x, x.property.1.1⟩, x.property.1⟩, x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨hAB.of_equiv e, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_inf (le_inf (inf_le_left.trans d.S_le_G1)
      ((inf_le_left.trans d.S_le_T).trans hTMc)) inf_le_right
  · exact lt_of_le_of_ne inf_le_right (fun he => d.L_not_le_MZ (he ▸ inf_le_left))
  · exact inf_le_inf_right _ (d.S_le_T.trans hTM)
  · exact lt_of_le_of_ne inf_le_right (fun he => s.outside_M (he ▸ inf_le_left))
  · exact fun x hx => ⟨⟨d.L_component.1 hx.1, hMc.2 hx.2⟩, hx.1⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
