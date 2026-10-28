module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Linear
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.SylowOvergroupNormalizer

/-!
# The complete initial higher-field exclusion

For Sp₄(2ⁿ), n > 1, the nonsolvable local intersection has a point or
plane local factor as its solvable residual. The concrete automorphism
kernel calculation and the original core normalizer place the whole
parabolic, hence the Borel, inside M_L. This discharges the missing Borel
premise of 15.1.21 before exchanged-component selection.

The solvable-local result handles the other case. Combining this with the
existing linear exclusion eliminates all of OrdinaryHigherField, including
the retained central two-covers of PSL₃(4). The original-marker application
keeps the same component data, Z₁, row and source prime.

The literal earlier 15.1.14 residual remains with
qt-e-1514-global-thompson-residual and final discharge in
qt-e-15122-pre-exclusion-catalogue. Exceptional higher-field exclusions,
initial exhaustion and Ordinary22 refinements remain with
qt-e-15122-ordinary-pre-exclusion.
Source: Aschbacher--Smith, 15.1.19--21, printed pp.1093--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original core normalizer forces Borel placement in the nonsolvable symplectic case. -/
theorem PreExclusionSource.symplectic_nonsolvable_parabolic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : d.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hns : ¬ Group.IsSolvable d.ML) : d.OrdinaryParabolic d.ML := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K := d.L.subgroupOf d.G1
  let N := d.MZ.subgroupOf d.G1
  let : K.Normal := s.higherField_normal (h := h) hG hL
    (.inl ⟨n,hn,.inr ⟨F,inferInstance,inferInstance,hF,
      ⟨e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩⟩)
  let eK : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let e' := e.symm.trans eK.symm
  let f := K.subtype.comp e'.toMonoidHom
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hQN : (Q : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)).map f ≤ N := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    have hm := ((s.ordinary hL).sylow_le_local (hP ▸ mem_map_of_mem d.L.subtype hz)).1
    change (e.symm (e z) : G) ∈ d.MZ
    rwa [e.symm_apply_apply]
  have hproper : N.comap f ≠ ⊤ := by
    intro ht
    apply d.L_not_le_MZ
    intro x hx
    have hh : e ⟨x,hx⟩ ∈ N.comap f := ht ▸ mem_top _
    change (e.symm (e ⟨x,hx⟩) : G) ∈ d.MZ at hh
    change x ∈ d.MZ
    rw [e.symm_apply_apply] at hh
    exact hh
  have hns' : ¬ Group.IsSolvable (N.comap f) := by
    intro hs
    let := hs
    let j : d.ML →* N.comap f := {
      toFun x := ⟨e ⟨x,x.property.2⟩,by
        change (e.symm (e ⟨x,x.property.2⟩) : G) ∈ d.MZ
        rw [e.symm_apply_apply]
        exact x.property.1⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' x y := by
        apply Subtype.ext
        exact map_mul e ⟨x,x.property.2⟩ ⟨y,y.property.2⟩ }
    apply hns
    apply Group.isSolvable_of_isSolvable_injective (f := j)
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : d.L => (x : G))
      (e.injective (congrArg Subtype.val hxy)))
  have hcore : normalizer (N.pCoreIn 2 : Set d.G1) ≤ N := by
    rw [pCoreIn_subgroupOf 2 d.MZ d.G1 (show d.MZ ≤ d.G1 from inf_le_left)]
    intro x hx
    have hm := le_normalizer_map d.G1.subtype (mem_map_of_mem d.G1.subtype hx)
    change (x : G) ∈ normalizer ((d.Q1.subgroupOf d.G1).map d.G1.subtype : Set G) at hm
    rw [map_subgroupOf_eq_of_le (d.Q1_le_MZ.trans inf_le_left)] at hm
    change (x : G) ∈ d.MZ
    rw [←s.core_normalizer]
    exact ⟨x.property,hm⟩
  have hb := Theory.SpecificGroups.SymplecticFour.nonsolvable_local_borel_le
    hF hn K N e' Q hQN hproper hns' hcore
  refine ⟨(s.ordinary hL).local_proper,?_⟩
  rintro x ⟨y,hy,rfl⟩
  refine ⟨?_,y.property⟩
  have hQ : e y ∈ normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
    change e y ∈ normalizer ((P : Subgroup d.L).map e.toMonoidHom : Set _)
    rw [←map_equiv_normalizer_eq]
    apply mem_map_of_mem
    rwa [hP']
  have hm := hb (mem_map_of_mem f hQ)
  change (e.symm (e y) : G) ∈ d.MZ at hm
  rwa [e.symm_apply_apply] at hm

/-- The whole symplectic higher-field branch is excluded before exchanged selection. -/
theorem PreExclusionSource.false_of_initial_symplectic_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : 1<n) (hm : ClassicalGroup.IsPSp d.L 2 (2^n)) : False := by
  by_cases hs : Group.IsSolvable d.ML
  · exact s.false_of_higherField_solvable (h := h) hG hM hJ hu hne hmany hres hL
      (.inl ⟨n,hn,.inr hm⟩) hs
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact s.false_of_symplectic_higherField (h := h) hG hM hJ hL hn
      ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
      (s.symplectic_nonsolvable_parabolic (h := h) hG hL hn hF
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm) hs)
/-- The initial higher-field linear, symplectic and retained central-cover rows are impossible. -/
theorem PreExclusionSource.false_of_initial_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) : False := by
  obtain ⟨n,hn,hm⟩ := s.higherField_symplectic (h := h) hG hempty hM hJ hu hne
    hmany hres hL hm
  exact s.false_of_initial_symplectic_higherField (h := h) hG hM hJ hu hne hmany hres hL hn hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- At the original marker, all higher-field linear/symplectic groups and the
retained central covers are excluded. The literal earlier residual remains for final assembly. -/
theorem PreparedChosenModule.source_preExclusion_no_higherField
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → ¬ d.OrdinaryHigherField) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hm => s.false_of_initial_higherField (h := h)
    hG hempty hM hJ hu hne hmany hres hL hm⟩
end CFSG.Quasithin.Chapter15.Section01
