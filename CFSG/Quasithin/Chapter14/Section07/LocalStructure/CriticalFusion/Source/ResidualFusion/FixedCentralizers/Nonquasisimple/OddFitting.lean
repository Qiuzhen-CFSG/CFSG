module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.SourceDichotomy
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ThreeFitting
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeFitting
public import Theory.SpecificGroups.SymmetricFive.RadicalRange
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Quotient
public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedCentralizer_characteristicTwo_before_quotient
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    {Lu : Subgroup G} (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hKLu : K F ≤ Lu) (hnq : ¬ IsQuasisimple Lu) :
    d.fixedCentralizer u ∈ Chapter1.He G := by
  have hzpoint : d.z ∈ F.Vi 1 := by rw [d.point]; exact mem_zpowers d.z
  have hzK : d.z ∈ K F :=
    le_normalizer_iff_commutator_le_right.mp
      (d.conjugationSection.section_le.trans (H_normalizes_K F)) d.point_mem_U_commutator_K
  have hd := Chapter1.lemma_1_2_11_involution d.counterexample.qtke T
    (d.fixedCentralizer u) Lu d.z (d.fixedCentralizer_core_ne_bot u hne) hsyl
    ⟨hLu,hc⟩ (d.fixedElement_order ⟨d.z,d.U₀_le_U d.z_mem_U₀⟩ d.z_ne_one)
    (hKLu hzK) (d.point_le_fixedSylow u hzpoint)
    (fun t ht => mem_centralizer_singleton_iff.mp
      (d.centralizer_eq ▸ F.invariant 1 ht))
    ⟨F.U,d.U_le_fixedCentralizer u,d.U_elementary,
      commutator_mono le_rfl (d.K_le_fixedNormalizer_residual u hu) d.point_mem_U_commutator_K⟩
    (d.fixedCentralizer_core_centralizer_le u)
  exact hd.resolve_left hnq

theorem fixedCentralizer_fitting_three
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H)
    (hchar : d.fixedCentralizer u ∈ Chapter1.He G) :
    IsPGroup 3 (fittingSubgroup ((d.fixedCentralizer u) ⧸ pCore 2 (d.fixedCentralizer u))) := by
  let M := (F.H ⊓ d.fixedCentralizer u : Subgroup G).subgroupOf (d.fixedCentralizer u)
  let e : M ≃* d.fixedJoin u := (subgroupOfEquivOfLe inf_le_right).trans
    (MulEquiv.subgroupCongr (d.fixedCentralizer_inter_H u hu))
  let f := (d.fixedJoinMap u).comp e.toMonoidHom
  have hr : f.range = (d.fixedJoinMap u).range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,← MonoidHom.range_eq_map]
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((d.fixedJoinMap u).ker).comap e.toMonoidHom)
    rw [d.fixedJoinMap_ker u hu hfix]
    exact pCore_isPGroup.comap_of_injective _ e.injective
  apply ChapterC.Section02Source.fitting_quotient_isThreeGroup
    (d.fixedCentralizer_sqtk u hne) ((d.fixedCore u).subgroupOf (d.fixedCentralizer u)) M
    (d.fixedCore_radical u hu hfix hmax)
    (d.fixedCore_intrinsic_characteristic_control u hu hfix hmax)
    (Chapter1.mem_He_iff.mp hchar)
  exact ChapterC.Section02Source.intersection_twoFittingCore_isTwoGroup M f
    (hr.symm ▸ d.alternating_le_fixedJoinMap_range u) hk

theorem fixedComponent_quotient_quasisimple_before_sieve
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    {Lu : Subgroup G} (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hKLu : K F ≤ Lu) (hnq : ¬ IsQuasisimple Lu) :
    IsQuasisimple (Lu ⧸ pCore 2 Lu) := by
  let : Group.IsNilpotent (pCore 2 (d.fixedCentralizer u)) := pCore_isPGroup.isNilpotent
  have hchar := d.fixedCentralizer_characteristicTwo_before_quotient u hu hne hsyl hLu hc hKLu hnq
  let := ChapterA.Section03.cComponent_quasisimple_of_fitting_three
    (d.fixedCentralizer_quotient_sqtk u hne) (pCore_quotient_pCore_eq_bot 2)
    (d.fixedCentralizer_fitting_three u hu hne hfix hmax hchar)
    (d.fixedComponentImage u Lu) (hc.map_quotient _)
  exact IsQuasisimple.of_mulEquiv (d.fixedComponentQuotientEquiv u hLu hc).symm

/-- The odd-fitting route packages the literal selected component into the
remaining C.2.7 input: its quotient quasisimplicity is proved from C.2.6 and
A.3.6, rather than carried as a premise. -/
theorem fixedComponent_case_of_source
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) (hNK : normalizer (K F : Set G) = F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    {Lu : Subgroup G} (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hKLu : K F < Lu) (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hout : ¬ Lu ≤ F.H) (hnq : ¬ IsQuasisimple Lu) :
    Nonquasisimple.Case d u Lu := by
  exact ⟨hu, hne, hfix, hNK, hmax, hsyl, hLu, hc,
    hKLu, hn, hout, hnq, by
      exact d.fixedComponent_quotient_quasisimple_before_sieve u hu hne hfix hmax hsyl hLu hc hKLu.le hnq⟩
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
