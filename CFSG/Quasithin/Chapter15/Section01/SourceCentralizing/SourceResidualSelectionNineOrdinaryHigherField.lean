module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineOrdinaryBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Symplectic

/-!
# Higher-field ordinary exclusions from the marked residual

The actual marked-residual normalizer bound gives the original solvable
Borel control. The concrete linear and symplectic model calculations then
identify a solvable local intersection with its Borel. The existing
higher-field exclusions apply to that proved placement; the nonsolvable
symplectic argument is independent of the global fixed-subgroup residual.

All source components, central covers, local intersections and Borels are
retained. No global 15.1.14 premise is used.
Source: Aschbacher--Smith 15.1.20--21, printed pp.1096--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem borel_characteristicTwo_of_surjective
    (s : d.PreExclusionSource h.normalized p)
    {X : Type*} [Group X] [Finite X] (f : d.L →* X)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hc : ∀ Q : Sylow 2 X, HasCharacteristicTwo (normalizer (Q : Set X))) :
    HasCharacteristicTwo d.ordinaryBorel := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  let B := normalizer (P : Set d.L)
  have hB : HasCharacteristicTwo B := by
    apply f.centralizer_pCore_subgroup_of_image hk
    rw [P.normalizer_map_surjective f hf]
    exact hc (P.mapSurjective hf)
  have hBG : B.map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  exact hB.of_equiv ((B.equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
    (MulEquiv.subgroupCongr hBG))
private theorem linear_quotient_solvable_borel_local
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hsol : Group.IsSolvable d.ML)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (f : d.L →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    d.ML = d.ordinaryBorel := by
  apply s.solvable_local_borel_eq_of_local_residual (h := h) hG hu hbound hL hsol
  · exact SolvableSylowControl.of_surjective_pKernel f hf hk
      (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
        F (by omega) hF)
  · exact borel_characteristicTwo_of_surjective (h := h) s f hf hk
      (Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_core_selfCentralizing
        F (by omega) hF)
private theorem symplectic_solvable_borel_local
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hsol : Group.IsSolvable d.ML)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : d.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    d.ML = d.ordinaryBorel := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  apply s.solvable_local_borel_eq_of_local_residual (h := h) hG hu hbound hL hsol
  · apply SolvableSylowControl.of_equiv e
    exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits
      hF hn (fun A hA hUA =>
        Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal hlarge A hA hUA)
  · apply borel_characteristicTwo_of_surjective (h := h) s e.toMonoidHom e.surjective
      (IsPGroup.ker_isPGroup_of_injective e.injective)
    intro Q
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv hF (by omega) Q)).mpr
        (Theory.SpecificGroups.SymplecticFour.borel_selfCentralizing_core hF hn)
/-- Higher-field models with solvable original local intersection are impossible. -/
theorem PreExclusionSource.false_of_higherField_solvable_of_local_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) (hsol : Group.IsSolvable d.ML) : False := by
  have hb : d.ML = d.ordinaryBorel := by
    rcases hm with ⟨n,hn,hm | hm⟩ | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact linear_quotient_solvable_borel_local (h := h) s hG hu hbound hL hsol hn hF
        e.toMonoidHom e.surjective (IsPGroup.ker_isPGroup_of_injective e.injective)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact symplectic_solvable_borel_local (h := h) s hG hu hbound hL hsol hn hF
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
      have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hk : IsPGroup 2 f.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
        exact pCore_isPGroup
      exact linear_quotient_solvable_borel_local (h := h) s hG hu hbound hL hsol
        (n := 2) (by decide) (by simpa using hF) f hf hk
  exact s.false_of_higherField (h := h) hG hM hJ hu hL hm
    ⟨(s.ordinary hL).local_proper,hb.ge⟩

/-- The original higher-field linear, symplectic, and central-cover alternatives
are excluded by the actual local residual bound. -/
theorem PreExclusionSource.false_of_initial_higherField_of_local_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) : False := by
  have hfalse := s.false_of_higherField_solvable_of_local_residual
    (h := h) hG hM hJ hu hbound hL hm
  rcases hm with ⟨n,hn,hm | hm⟩ | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact hfalse (s.linear_local_solvable (h := h) hG hempty hM hu hL (by omega) hF e)
  · by_cases hs : Group.IsSolvable d.ML
    · exact hfalse hs
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact s.false_of_symplectic_higherField (h := h) hG hM hJ hL hn
        ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
        (s.symplectic_nonsolvable_parabolic (h := h) hG hL hn hF
          (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm) hs)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact hfalse (s.linear_quotient_local_solvable (h := h) hG hempty hM hu hL
      (n := 2) (by decide) (by simpa using hF) e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
