module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Core
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# The literal MS pair for the preliminary linear-three reduction

For QI = O₂(KS), uniqueness controls normalizers of its nontrivial
characteristic subgroups. An escaping X₀ therefore satisfies MS3 relative
to X₀QI. This extension inherits characteristic two, and S ∩ X₀QI is
its Sylow subgroup. The original ZS lies in that Sylow's omega center,
so the central-omega clause of C.1.34(5) contradicts escape.

The centralizer marking C_X₀(ZS) ≤ KS constructs MS2(a) using the actual
odd-index centralizer. This marking, component-orbit reduction, and the
comparison of the local omega centralizer with C_X₀QI(ZS) remain with
qt-e-152-char2-block-exclusion. This module does not assert those inputs
or the complete preliminary linear-three exclusion. Earlier Kc inputs
retain their original producers and final plane-uniqueness discharge.

Source: Aschbacher--Smith, preliminary 15.2.23, pp.1115--1116,
and C.1.31--34, pp.135--137, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Uniqueness controls each nontrivial characteristic subgroup of QI. -/
theorem planeParabolicCore_characteristic_normalizer_le
    (hI : PlaneEscapes Mc ZS I)
    (C : Subgroup (planeParabolicCore T H ZS)) [C.Characteristic] (hne : C ≠ ⊥) :
    normalizer (C.map (planeParabolicCore T H ZS).subtype : Set G) ≤ Mc := by
  apply d.normalizer_le_partner_of_seed_normal
  · exact ((isPGroup_pCoreIn 2 _).to_subgroup C).map _
  · exact fun hz => hne ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  · exact (d.planeParabolicCore_normalized hI).trans
      (normalizer_le_normalizer_characteristic_image _ C)

/-- MS3 holds relative to the literal join X₀QI. -/
theorem plane_ms_characteristic
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc) :
    MSNoCharacteristicNormal X0 (planeParabolicCore T H ZS) := by
  intro C hC hn
  let := hC
  by_contra hne
  have hCE : C.map (planeParabolicCore T H ZS).subtype ≤
      X0 ⊔ planeParabolicCore T H ZS := (map_subtype_le _).trans le_sup_right
  have hnorm := (normal_subgroupOf_iff_le_normalizer hCE).mp hn
  exact hout (le_sup_left.trans (hnorm.trans
    (d.planeParabolicCore_characteristic_normalizer_le hI C hne)))

/-- The extension contains O₂(I), so it inherits characteristic two. -/
theorem plane_extension_fitting
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) :
    generalizedFitting (X0 ⊔ planeParabolicCore T H ZS : Subgroup G) =
      pCore 2 (X0 ⊔ planeParabolicCore T H ZS : Subgroup G) := by
  let E := X0 ⊔ planeParabolicCore T H ZS
  have hEI : E ≤ I := sup_le hXI ((pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  have hcore : I.pCoreIn 2 ≤ planeParabolicCore T H ZS := by
    have hh : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
      (d.core_le_plane hI).trans le_sup_right
    simpa only [inf_eq_right.mpr hh] using
      inf_pCoreIn_le_of_le 2 ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hcore' : pCore 2 I ≤ E.subgroupOf I := fun x hx =>
    mem_sup_right (hcore (mem_map_of_mem I.subtype hx))
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hEI)).mp
    (centralizer_pCore_le_of_pCore_le (E.subgroupOf I)
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) hcore')

/-- Restrict S to the extension, retaining its original embedding. -/
theorem plane_extension_sylow
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G)) :
    Chapter1.IsSylowIn 2
      (planeSylow T ZS ⊓ (X0 ⊔ planeParabolicCore T H ZS))
      (X0 ⊔ planeParabolicCore T H ZS) := by
  let Q := planeParabolicCore T H ZS
  let E := X0 ⊔ Q
  have hSI : planeSylow T ZS ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hEI : E ≤ I := sup_le hXI ((d.planeParabolicCore_le_plane hI).trans hSI)
  have hSQ : planeSylow T ZS ≤ normalizer (Q : Set G) :=
    (inf_le_left.trans d.geometry.outside.1.1.2).trans (d.planeParabolicCore_normalized hI)
  have hSE : planeSylow T ZS ≤ normalizer (E : Set G) :=
    (le_inf (hSI.trans hn) hSQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hn' : (P : Subgroup I) ≤ normalizer (E.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hEI]
    intro x hx
    exact hSE (hP ▸ mem_map_of_mem I.subtype hx)
  have hs := Chapter1.Terminal.sylow_inf_of_normalizes P (E.subgroupOf I) hn'
  have hh := Chapter1.Section02.IndexTwo.isSylowIn_map hs I.subtype
  rwa [Subgroup.map_inf _ _ _ I.subtype_injective, hP, map_subgroupOf_eq_of_le hEI] at hh

/-- The marked centralizer gives the proper odd-index subgroup in MS2(a). -/
theorem plane_ms_odd_index
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G)) (hout : ¬ X0 ≤ Mc)
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS) :
    MSOddIndex X0 (planeParabolicCore T H ZS) := by
  let E := X0 ⊔ planeParabolicCore T H ZS
  let C := E ⊓ centralizer (ZS : Set G)
  have hCE : C < E := lt_of_le_of_ne inf_le_left (by
    intro he
    have hEC : E ≤ centralizer (ZS : Set G) :=
      he ▸ (show C ≤ centralizer (ZS : Set G) from inf_le_right)
    exact hout (le_sup_left.trans hEC |>.trans
      ((d.centralizer_le_intersection hI).trans inf_le_left)))
  obtain ⟨P,hP⟩ := d.plane_extension_sylow hI hXI hn
  have hPC : (P : Subgroup E) ≤ C.subgroupOf E := by
    intro p hp
    have hh := hP ▸ mem_map_of_mem E.subtype hp
    exact ⟨p.property, hh.1.2⟩
  refine ⟨C,hCE,?_,d.plane_span_centralizer_core hI hn hmark
    (d.plane_block_centralizer_normalized hI hn)⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPC))

/-- The original plane lies in the actual local Sylow omega center. -/
theorem plane_extension_omega_contains
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (X0 : Subgroup G) :
    ZS ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (planeSylow T ZS ⊓ (X0 ⊔ planeParabolicCore T H ZS)) := by
  intro z hz
  have hzs := (mem_omegaOneCenterAmbient_iff _ _).mp (d.omega_center ▸ hz)
  change z ∈ omegaOneCenterAmbient _
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  exact ⟨⟨hzs.1,mem_sup_right (d.plane_le_planeParabolicCore hI hfit hz)⟩,
    hzs.2.1,fun s hs => hzs.2.2 s hs.1⟩

/-- The central-omega clause of C.1.34(5) contradicts escape from Mc. -/
theorem plane_extension_omega_not_central
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc) :
    ¬ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (planeSylow T ZS ⊓ (X0 ⊔ planeParabolicCore T H ZS)) ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (X0 ⊔ planeParabolicCore T H ZS) := by
  intro hc
  apply hout
  apply le_trans ?_ ((d.centralizer_le_intersection hI).trans inf_le_left)
  intro x hx z hz
  obtain ⟨a,ha,he⟩ := hc (d.plane_extension_omega_contains hI hfit X0 hz)
  have hh := congrArg Subtype.val
    (mem_center_iff.mp ha (⟨x,mem_sup_left hx⟩ : (X0 ⊔ planeParabolicCore T H ZS : Subgroup G)))
  change x * (a : G) = (a : G) * x at hh
  change (a : G) = z at he
  rw [he] at hh
  exact hh.symm

/-- Construct the genuine MS pair from the component, quotient and centralizer marking. -/
theorem plane_linearThree_msPair
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hX : X0 ∈ Chapter1.cComponentsIn I)
    (hn : I ≤ normalizer (X0 : Set G)) (hout : ¬ X0 ≤ Mc)
    {n : ℕ} {F : Type} [Field F] [Finite F]
    (hnpos : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : Chapter1.XiQuotient X0 ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS) :
    LinearThreeMSPair KnownSimple.IsKnownSimple X0 (planeParabolicCore T H ZS) n F := by
  have hEI : X0 ⊔ planeParabolicCore T H ZS ≤ I := sup_le hX.1
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  refine ⟨hnpos,hF,⟨e⟩,?_,d.plane_extension_fitting hI hfit hX.1,?_,
    Or.inl (d.plane_ms_odd_index hI hX.1 hn hout hmark),d.plane_ms_characteristic hI hout⟩
  · exact (IsSQTK.equiv (subgroupOfEquivOfLe hEI)).mp
      ((Chapter3.sqtk_of_mem_H hsource.ambient hI.1).subgroup _)
  · exact ⟨le_sup_left,hX.2.subgroupOf_of_le le_sup_left hEI⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
