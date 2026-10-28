module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.SolvableBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Complete
public import Theory.GroupTheory.SolvableSylowControl.PrimeKernel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.BorelLocalCover

/-!
# The solvable-local higher-field family before exchanged selection

For PSL₃(2ⁿ), Sp₄(2ⁿ), n > 1, and every retained central two-cover of
PSL₃(4), the concrete model controls solvable Sylow overgroups and gives
characteristic two of the Borel. SolvableBorel therefore identifies the
original M_L with that Borel. The proved 15.1.21 exclusions apply with
their literal parabolic hypothesis now discharged.

The actual original-marker consumer concludes that any surviving
higher-field model has nonsolvable M_L, retaining its component, prime
and markings. No exchanged-source premise is used. The nonsolvable-local
cases, other higher-field families, full initial exhaustion and Ordinary22
remain with qt-e-15122-ordinary-pre-exclusion. The literal earlier residual
input retains its existing producer and final pre-exclusion assembly owner.
Source: Aschbacher--Smith 15.1.20(3b), 15.1.21, pp.1096--1098.
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

variable
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hsol : Group.IsSolvable d.ML)

include s hG hM hu hne hmany hres hL hsol in
/-- The original solvable local intersection is the Borel, retaining a two-group kernel. -/
theorem PreExclusionSource.linear_quotient_solvable_borel
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (f : d.L →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    d.ML = d.ordinaryBorel := by
  apply s.solvable_local_borel_eq (h := h) hG hM hu hne hmany hres hL hsol
  · exact SolvableSylowControl.of_surjective_pKernel f hf hk
      (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
        F (by omega) hF)
  · exact borel_characteristicTwo_of_surjective (h := h) s f hf hk
      (Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_core_selfCentralizing
        F (by omega) hF)

include s hG hM hu hne hmany hres hL hsol in
/-- The actual symplectic model identifies the original solvable local intersection with its Borel. -/
theorem PreExclusionSource.symplectic_solvable_borel
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : d.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    d.ML = d.ordinaryBorel := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  apply s.solvable_local_borel_eq (h := h) hG hM hu hne hmany hres hL hsol
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

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Every higher-field constructor is impossible when its original local intersection is solvable. -/
theorem PreExclusionSource.false_of_higherField_solvable
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
    (hm : d.OrdinaryHigherField) (hsol : Group.IsSolvable d.ML) : False := by
  have hb : d.ML = d.ordinaryBorel := by
    rcases hm with ⟨n,hn,hm | hm⟩ | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact s.linear_quotient_solvable_borel (h := h) hG hM hu hne hmany hres hL hsol hn hF
        e.toMonoidHom e.surjective (IsPGroup.ker_isPGroup_of_injective e.injective)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact s.symplectic_solvable_borel (h := h) hG hM hu hne hmany hres hL hsol hn hF
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
      have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hk : IsPGroup 2 f.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
        exact pCore_isPGroup
      exact s.linear_quotient_solvable_borel (h := h) hG hM hu hne hmany hres hL hsol
        (n := 2) (by decide) (by simpa using hF) f hf hk
  exact s.false_of_higherField (h := h) hG hM hJ hu hL hm
    ⟨(s.ordinary hL).local_proper,hb.ge⟩

/-- A remaining higher-field model must have a nonsolvable original M_L. -/
theorem PreExclusionSource.higherField_local_not_solvable
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
    (hm : d.OrdinaryHigherField) : ¬ Group.IsSolvable d.ML :=
  s.false_of_higherField_solvable (h := h) hG hM hJ hu hne hmany hres hL hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- At the original marker, the surviving higher-field branch has nonsolvable M_L.
The literal earlier residual premise is retained for the final source assembly. -/
theorem PreparedChosenModule.source_preExclusion_higherField_local_not_solvable
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinaryHigherField →
        ¬ Group.IsSolvable d.ML) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hm => s.higherField_local_not_solvable (h := h)
    hG hM hJ hu hne hmany hres hL hm⟩
end CFSG.Quasithin.Chapter15.Section01
