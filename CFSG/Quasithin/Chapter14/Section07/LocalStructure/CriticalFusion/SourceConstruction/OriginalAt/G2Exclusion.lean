module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.G2FourCycle
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Kernel

/-!
# Excluding the original G₂ residual with local structure

The original section kernel gives the faithful star action. Criticality
and the no-transvection theorem force a nonzero actor. Construct and orient
its critical path, then apply the reciprocal-line four-cycle contradiction.
The last theorem supplies this exclusion to the actual Data constructor.
The core identity and orbit inputs remain explicit in this intermediate API.

Only Structural1222At at the original G,T is used. The source producers
qt-d-1222-source and qt-d-1434-source retain the earlier structural and
faithful inputs. Original residual alternatives, uniqueness, relative
component and alternating recognition retain qt-d-14763-source-data.
Final source 14.7.75 discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.53–63, pp.1065–1069; F.9.18, pp.325–326.
The reused concrete model calculations retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

private theorem star_residual_at : star F (K F) = pResidual 2 (HStar F.H) := by
  rw [CriticalFusion.Source.star,LocalReduction.residual_subgroupOf]
  exact map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)

private theorem source_g2_component_properties_at
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    generalizedFitting (HStar F.H) = star F (K F) ∧
      centralizer (star F (K F) : Set (HStar F.H)) = ⊥ ∧ IsQuasisimple (star F (K F)) := by
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup (star F (K F)) := e.isSimpleGroup
  let : Group.IsPerfect (star F (K F)) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : (star F (K F)).Normal := star_residual_at (F := F) ▸ inferInstance
  have hp : IsPGroup 2 ((HStar F.H) ⧸ star F (K F)) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (star_residual_at (F := F)).symm)
  have hs := simple_two_quotient_structure (star F (K F))
    (Group.IsPerfect.not_isMulCommutative _) hp (pCore_quotient_pCore_eq_bot 2)
  have hz : center (star F (K F)) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  exact ⟨hs.1,hs.2.1,⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩⟩

include c in
private theorem source_star_faithful_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G)) : Function.Injective σ := by
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply le_bot_iff.mp
  intro a ha
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) a
  have hk := LocalReduction.section_action_kernel_eq_core_of_escape_at h structural hescape c
  have hqa : a ∈ pCore 2 F.H := hk ▸ ha
  exact (QuotientGroup.eq_one_iff _).mpr hqa

include c in
theorem source_critical_star_ne_bot_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (path : CriticalPath (L := L) F) : star F path.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨hfit,hcent,hq⟩ := source_g2_component_properties_at hcomponent eK
  let := hq
  let : (star F (K F)).Normal := star_residual_at (F := F) ▸ inferInstance
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  intro hz
  have hAH : path.Uα ≤ F.H := (LocalReduction.critical_le_Q_at h structural path).trans (Q_le_H F)
  have hαQ : path.Uα ≤ F.H.pCoreIn 2 := by
    have hk : path.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  let φ := (MulAut.conj path.conjugator).toMonoidHom
  let A := F.U.map φ
  let C := (F.Vi 1).map φ
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hmap : path.Uα.map φ = F.U := conjBy_inv' _ _
  have hA : A ≤ F.H := by
    have hh := map_mono (f := φ) (reciprocal_placement h path)
    change A ≤ (F.H.conjBy path.conjugator⁻¹).conjBy path.conjugator at hh
    rwa [conjBy_inv'] at hh
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hh := map_mono (f := φ) ((commutator_mono le_rfl hαQ).trans_eq hcomm)
    rwa [map_commutator,hmap] at hh
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj path.conjugator).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro x hx
    let a : F.H := ⟨x,hA hx⟩
    have hdim := c.displacement_rank_le_of_commutator_bound A C ⊥ bot_le hc 1
      (by simpa only [relIndex_bot_left,pow_one] using hC) a hx
    have hzstar : starMap F a = 1 := by
      by_contra hn
      have hpow : starMap F a ^ 2 = 1 := by
        rw [←map_pow]
        have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨x,hx⟩ : A)
        have ha2 : a ^ 2 = 1 := Subtype.ext (congrArg (fun z : A => (z:G)) hh)
        rw [ha2,map_one]
      have hn' := Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.no_transvection
        σ (star F (K F)) hf hcent e (starMap F a) hn hpow
      have hp := fixedCodim_pos_of_faithful σ hf
        (show zpowers (starMap F a) ≠ ⊥ by simpa using hn)
      rw [fixedCodim_zpowers_eq_displacement_rank] at hp hn'
      change Module.finrank (ZMod 2) (σ (starMap F a) - LinearMap.id).range ≤ 1 at hdim
      omega
    exact mem_map.mpr ⟨a,(QuotientGroup.eq_one_iff _).mp hzstar,rfl⟩
  apply LocalReduction.critical_span_not_le_reciprocal_core path
  intro x hx
  change x ∈ (conjugate F.H path.conjugator).pCoreIn 2
  unfold conjugate
  rw [←map_pCoreIn_of_injective 2 F.H (MulAut.conj path.conjugator⁻¹).toMonoidHom
    (MulAut.conj path.conjugator⁻¹).injective]
  refine ⟨φ x,hAQ (mem_map_of_mem φ hx),?_⟩
  simp [φ,MulAut.conj_apply,mul_assoc]

theorem source_not_g2_residual_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (orbit : letI := h.chosen.elementary
      letI := hab
      letI := elementary_U F
      ∀ σ : Representation (ZMod 2) (HStar F.H) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),
      BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)) →
      let P : Sylow 2 (HStar F.H) :=
        (T.subtype (F.invariant 1)).mapSurjective
          (QuotientGroup.mk'_surjective (pCore 2 F.H))
      OrbitInputs σ (pResidual 2 (HStar F.H)) P (pResidual_sup_sylow_eq_top P)) :
    ¬ G2Residual F := by
  rintro ⟨eK⟩
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := LocalReduction.exists_star_representation h s
  rw [←hσ] at s
  have hescape : ¬ F.H ≤ normalizer (L : Set G) := by
    have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) := hunique.symm ▸ Set.mem_singleton _
    exact hh.2.2
  have hf := source_star_faithful_at s h structural hescape
  obtain ⟨hfit,_,_⟩ := source_g2_component_properties_at hcomponent eK
  obtain ⟨path⟩ := LocalReduction.exists_criticalPath_at h hab hescape structural
  obtain ⟨path,selection⟩ := LocalReduction.select_critical_orientation_of_nontrivial_star_at
    h structural path (source_critical_star_ne_bot_at s h hab hcomponent eK hf hcomm structural path)
  let P : Sylow 2 (HStar F.H) :=
    (T.subtype (F.invariant 1)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 F.H))
  have hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤ := by
    rw [star_residual_at]
    exact pResidual_sup_sylow_eq_top P
  let : (star F (K F)).Normal := star_residual_at (F := F) ▸ inferInstance
  have horbit : OrbitInputs σ (star F (K F)) P hP := by
    simpa only [star_residual_at] using orbit σ s
  exact source_critical_contradiction_at s h hab hcomponent hfit eK structural hf hcomm
    P hP horbit path selection

theorem exists_data_of_g2_exclusion_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (orbit : letI := h.chosen.elementary
      letI := hab
      letI := elementary_U F
      ∀ σ : Representation (ZMod 2) (HStar F.H) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),
      BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)) →
      let P : Sylow 2 (HStar F.H) :=
        (T.subtype (F.invariant 1)).mapSurjective
          (QuotientGroup.mk'_surjective (pCore 2 F.H))
      OrbitInputs σ (pResidual 2 (HStar F.H)) P (pResidual_sup_sylow_eq_top P))
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) :=
  exists_data_of_source_branches d h hab hunique hcomponent h52
    (source_not_g2_residual_at h hab hunique hcomponent structural hcomm orbit) h40

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
