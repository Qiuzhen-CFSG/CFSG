module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSolvableControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.Borel
public import Theory.GroupTheory.SolvableSylowControl

/-!
# Original ordinary Borels from the marked residual normalizer

The marked residual normalizer bound controls the component orbit of the
actual Sylow Borel. For a solvable original local intersection, or an
original rank-one component, this gives the reverse inclusion and identifies
that intersection with its actual Borel. Only the literal local bound on
O²(M_Z) is used; global fixed-subgroup residual centralization is not assumed.

The rank-one constructor keeps the original component, marking, and module.
Its centralizer placement still uses the original maximal-local hypothesis.
Source: Aschbacher--Smith 15.1.19(2), 15.1.20(3), printed pp.1093--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem borel_core (s : d.PreExclusionSource h.normalized p) :
    d.ordinaryBorel.pCoreIn 2 = d.SL := by
  have hb : d.ordinaryBorel = d.L ⊓ normalizer (d.SL : Set G) := by
    unfold ordinaryBorel
    rw [←subgroupOf_normalizer_eq d.SL_le_L,subgroupOf_map_subtype]
    exact inf_comm _ _
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSB : d.SL ≤ d.ordinaryBorel := by
    rw [hb]
    exact le_inf d.SL_le_L d.SL.le_normalizer
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.ordinaryBorel ≤ d.L from map_subtype_le _) (hP ▸ hSB)
  apply le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le (d.SL_le_S.trans d.S_le_T))
    hSB (hb ▸ inf_le_right)

private theorem borel_odd (s : d.PreExclusionSource h.normalized p) :
    Odd (Nat.card (d.ordinaryBorel ⧸ pCore 2 d.ordinaryBorel)) := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSB : d.SL ≤ d.ordinaryBorel := by
    intro x hx
    exact ⟨⟨x,d.SL_le_L hx⟩,(d.SL.subgroupOf d.L).le_normalizer hx,rfl⟩
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.ordinaryBorel ≤ d.L from map_subtype_le _) (hP ▸ hSB)
  have he : pCore 2 d.ordinaryBorel = (Q : Subgroup d.ordinaryBorel) := by
    apply map_injective d.ordinaryBorel.subtype_injective
    exact (borel_core (h := h) s).trans (hQ.trans hP).symm
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hd : 2 ∣ (pCore 2 d.ordinaryBorel).index := even_iff_two_dvd.mp heven
  rw [he] at hd
  exact Q.not_dvd_index hd

/-- Solvable local intersection and intrinsic model control identify the literal Borel. -/
theorem PreExclusionSource.solvable_local_borel_eq_of_local_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hsol : Group.IsSolvable d.ML) (hc : SolvableSylowControl 2 d.L)
    (hB : HasCharacteristicTwo d.ordinaryBorel) :
    d.ML = d.ordinaryBorel := by
  let := hsol
  obtain ⟨P,hP⟩ := s.component_sylow
  have hcore : d.ML.pCoreIn 2 = d.SL := by
    have hh := SolvableSylowControl.core_intersection d.L d.ML hc P (hP ▸ (s.ordinary hL).sylow_le_local)
    rw [inf_eq_left.mpr (s.ordinary hL).local_proper.le,hP] at hh
    exact hh
  have hnA : d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.ML : Set G) :=
    (le_inf (inf_le_left.trans d.MZ.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hnP : d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.SL : Set G) := by
    rw [← hcore]
    exact hnA.trans (normalizer_le_normalizer_characteristic_image d.ML (pCore 2 d.ML))
  have hb : d.ordinaryBorel = d.L ⊓ normalizer (d.SL : Set G) := by
    unfold ordinaryBorel
    rw [←subgroupOf_normalizer_eq d.SL_le_L,subgroupOf_map_subtype]
    exact inf_comm _ _
  have hinv : d.MZ ⊓ normalizer (d.L : Set G) ≤ normalizer (d.ordinaryBorel : Set G) := by
    rw [hb]
    exact (le_inf inf_le_right (hnP.trans (normalizer (d.SL : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hupper : d.ML ≤ d.ordinaryBorel := by
    rw [hb]
    refine le_inf (s.ordinary hL).local_proper.le ?_
    rw [←hcore]
    exact d.ML.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.ML (pCore 2 d.ML))
  have hBL : d.ordinaryBorel ≤ d.L := map_subtype_le _
  obtain ⟨hf,ho⟩ := hL.relative_local_orbit_fitting_odd d.L_component.1 hBL
    (show d.MZ ≤ d.G1 from inf_le_left) hinv hB (borel_odd (h := h) s)
  have hBG : componentOrbit d.ordinaryBorel d.MZ ≤ d.G1 := by
    apply iSup_le
    intro a
    rintro x ⟨b,hb,rfl⟩
    exact d.G1.mul_mem (d.G1.mul_mem a.property.1 (d.L_component.1 (hBL hb)))
      (d.G1.inv_mem a.property.1)
  have hle := s.constrained_solvable_control_of_local_residual (h := h) hG hu hbound hBG
    (le_normalizer_componentOrbit _ _) hf ho
  exact le_antisymm hupper (le_inf ((le_componentOrbit _ _).trans hle) hBL)

/-- Original 15.1.19(2) forces the invariant orbit Borel into M_Z, giving the missing reverse inclusion. -/
theorem PreExclusionSource.rankOne_borel_eq_of_centralizer_le_of_local_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hc : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML) :
    d.ML = d.ordinaryBorel := by
  have hinv := s.rankOne_borel_normalized (h := h) hL hm
  have hBL : d.ordinaryBorel ≤ d.L := map_subtype_le _
  obtain ⟨hf,ho⟩ := hL.relative_local_orbit_fitting_odd d.L_component.1 hBL
    (show d.MZ ≤ d.G1 from inf_le_left) hinv
    (s.rankOne_borel_characteristicTwo (h := h) hL hm hc)
    (borel_odd (h := h) s)
  have hBG : componentOrbit d.ordinaryBorel d.MZ ≤ d.G1 := by
    apply iSup_le
    intro a
    rintro x ⟨b,hb,rfl⟩
    exact d.G1.mul_mem (d.G1.mul_mem a.property.1 (d.L_component.1 (hBL hb)))
      (d.G1.inv_mem a.property.1)
  have hle := s.constrained_solvable_control_of_local_residual (h := h) hG hu hbound hBG
    (le_normalizer_componentOrbit _ _) hf ho
  exact le_antisymm (s.rankOne_borel_bound (h := h) hL hm)
    (le_inf ((le_componentOrbit _ _).trans hle) hBL)


/-- The whole initial rank-one family, including central two-covers of Sz(8),
with its actual Borel clause proved from the original source hypotheses. -/
theorem PreExclusionSource.ordinary20_of_rankOne_of_local_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) : d.Ordinary20Alternatives := by
  exact .rankOne hm (s.rankOne_borel_eq_of_centralizer_le_of_local_residual (h := h) hG hu hbound hL hm
    (s.rankOne_centralizer_le (h := h) hG hM hu hL hm))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
