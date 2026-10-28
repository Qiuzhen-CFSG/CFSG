module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.GeometryInput
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Hall
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.LinearThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Movement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.MovingSupport
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.PResidual.Restriction

/-!
# Source placement and centralization in the nonzero fixed branch

The original Cartan construction supplies an odd Hall subgroup of H∩M.
Hall faithfulness and the binary-three automorphism calculation place it
inside the actual L₀. The Hall/Sylow supplement puts H∩M in L₀T, and
functoriality places its literal two-residual in L₀. The positive-kernel
natural-module argument proves that L₀ centralizes Ω₁Z(T); the residual
and Sylow supplement then prove the same for H∩M.

All subgroups and quotient maps retain the original fundamental setup.
The multiple-overgroup guard supplies Thompson movement; no minimal
reselection, fixed-space vanishing, TI, or later centralizer data is used
in the omega-center argument. Earlier Hall faithfulness stays explicit,
with final discharge owned by qt-d-10-fixed-hstar-parameter.
The stronger maximal-parabolic placement and wreath identification remain
open in this theorem family.
Source: Aschbacher--Smith 10.2.3(3), 10.2.8(1), and 10.3.1,
printed pp.744--745,749--750,755--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Original 10.2.8(1) on the whole component orbit and prescribed Sylow. -/
theorem orbit_centralizes_sylow_seed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    localOrbit T L ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have hm : PointControl.Selection.BinaryThreeNatural D := ⟨s.quotient, ⟨s.natural⟩⟩
  have hn : sourceMovedFixed D ≠ ⊥ := moved_fixed_ne_bot D s hfix
  have hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.fullModule : Set G) := by
    rw [s.full_eq_local]
    exact PointControl.Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot D hmany hfix
  have hc := PointControl.Selection.BinaryThree.core_omega_orbit_movement_le D hm hn
    s.full_eq_local hJ s.exchange_mem s.exchange_moves s.crossed
  have hz := PointControl.Selection.BinaryThree.orbit_centralizes_sylow_omega_of_commutator_le
    D hm hn s.full_eq_local (Bender.survivor_nonnormal s)
    (PointControl.Selection.BinaryThree.core_omega_component_movement_le_of_orbit_movement_le D hc)
  apply hz.trans
  apply centralizer_le
  intro z hz
  obtain ⟨hzt,hz2,hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨hzt,hzc,hz2⟩

/-- Hall placement and its Sylow supplement put the entire overlap in L₀T. -/
theorem overlap_le_localJoin
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ D.maximalLocal ≤ localJoin T L := by
  have hlarge : 1 < generationParameter H := by rw [s.generation H hH]; decide
  obtain ⟨hP,f,_,_,d,he,hperm,_⟩ := source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hBM := he ▸ d.hall_le
  have hHall := he ▸ d.hall
  have hb := MovingHall.linear_three_hall_le_orbit D (Bender.survivor_nonnormal s)
    hBM d.witness.odd
    (Bender.survivor_hall_faithful hfaith hmany s hH _ hBM hHall d.witness.abelian hperm)
    s.quotient
  let P := D.maximalLocal.subgroupOf H
  have hTP : (T.subtype hH.1.1.2 : Subgroup H) ≤ P := by
    intro t ht
    exact (le_normalizer_componentOrbit L T) ht
  have hg := congrArg (map P.subtype)
    (OddHall.sylow_complement_of_hall ((T.subtype hH.1.1.2).subtype hTP) hHall).sup_eq_top
  simp only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP,
    ← MonoidHom.range_eq_map, range_subtype] at hg
  have hBmap : (d.witness.abelianGroup.subgroupOf P).map P.subtype = d.witness.abelianGroup :=
    map_subgroupOf_eq_of_le hBM
  rw [hBmap] at hg
  have hp : P ≤ (localJoin T L).subgroupOf H := by
    rw [←hg]
    refine sup_le ?_ ?_
    · intro t ht
      exact (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) ht
    · intro b hb'
      exact (show localOrbit T L ≤ localJoin T L from le_sup_left)
        (hb (mem_map_of_mem H.subtype hb'))
  intro x hx
  exact hp (show (⟨x,hx.1⟩ : H) ∈ P from hx.2)

/-- The original maximal-local overlap equals its intersection with L₀T. -/
theorem overlap_eq_inf_localJoin
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ D.maximalLocal = H ⊓ localJoin T L := by
  apply le_antisymm
  · exact le_inf inf_le_left (overlap_le_localJoin D hfaith hmany s hH)
  · exact inf_le_inf_left H
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))

/-- The overlap has no prime divisors other than two and three. -/
theorem overlap_isSixGroup
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsPGroup 6 (H ⊓ D.maximalLocal : Subgroup G) := by
  rw [overlap_eq_inf_localJoin D hfaith hmany s hH]
  exact CentralHall.LinearThree.source_proper_overgroup_six D s.quotient
    (Bender.survivor_nonnormal s) _ (le_inf hH.1.1.2 le_sup_right)
    (CentralHall.LinearThree.source_hstar_inf_localJoin_lt D hH)

/-- The actual O²(H∩M), mapped by its subtype, lies in the original L₀. -/
theorem overlap_residual_le_orbit
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (pResidual 2 (H ⊓ D.maximalLocal : Subgroup G)).map
      (H ⊓ D.maximalLocal).subtype ≤ localOrbit T L := by
  let J := localJoin T L
  let R := (localOrbit T L).subgroupOf J
  have hRJ : localOrbit T L ≤ J := le_sup_left
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hgen : R ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRJ,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsPGroup 2 (J ⧸ R) := isPGroup_quotient_of_sup_eq_top R
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hgen
  have hres : (pResidual 2 J).map J.subtype ≤ localOrbit T L := by
    rintro x ⟨y,hy,rfl⟩
    exact (show pResidual 2 J ≤ R from sInf_le ⟨inferInstance,hq⟩) hy
  exact (embedded_pResidual_mono 2 (overlap_le_localJoin D hfaith hmany s hH)).trans hres

/-- The second clause of QuotientGeometryAt, with its source inputs discharged. -/
theorem overlap_centralizes_sylow_seed
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ D.maximalLocal ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have hTP : (T : Subgroup G) ≤ H ⊓ D.maximalLocal :=
    le_inf hH.1.1.2 (le_normalizer_componentOrbit L T)
  have hg := congrArg (map (H ⊓ D.maximalLocal).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
  simp only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP,
    ← MonoidHom.range_eq_map, range_subtype] at hg
  rw [←hg]
  refine sup_le ((overlap_residual_le_orbit D hfaith hmany s hH).trans
    (orbit_centralizes_sylow_seed D hmany s hfix)) ?_
  intro t ht z hz
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
