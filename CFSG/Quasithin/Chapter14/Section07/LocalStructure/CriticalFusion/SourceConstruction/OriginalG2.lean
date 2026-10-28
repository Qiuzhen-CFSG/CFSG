module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalCore
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.QuadraticConstituent

/-!
# The original G₂ exclusion with its earlier local inputs discharged

The actual residual and its two-group quotient give a self-centralizing
simple component in H/O₂(H). The original section kernel makes the star
action faithful. A critical path and its selected orientation are then
constructed on that same section. Its quadratic actor and literal common
line force the whole section to be Irr⁺, and give both F.9.18 orbit ratios.

The core commutator is derived before recognition: otherwise the residual
would be faithful, contradicting the two actual quotient models in14.3.4.
Thus the existing four-cycle exclusion applies without an assumed core
identity or orbit input. The final consumer constructs Data from the actual
alternating recognition branch. Structural1222 and EarlierFaithfulClassification
retain producers qt-d-1222-source and qt-d-1434-source; uniqueness, component
selection and alternating recognition remain with qt-d-14763-source-data.
Final original14.7.75 assembly remains with qt-d-14775-source.

Source: Aschbacher–Smith14.5.21(2),14.7.53–54 and14.7.63,
printed pp.1019,1065–1069; F.9.18(3–4), pp.325–326.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalG2
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

private theorem residual_star : star F (K F) = pResidual 2 (HStar F.H) := by
  rw [CriticalFusion.Source.star,LocalReduction.residual_subgroupOf]
  exact map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)

private theorem component_properties
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple (star F (K F)) ∧ center (star F (K F)) = ⊥ ∧
      centralizer (star F (K F) : Set (HStar F.H)) = ⊥ := by
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup (star F (K F)) := e.isSimpleGroup
  let : Group.IsPerfect (star F (K F)) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : (star F (K F)).Normal := residual_star (F := F) ▸ inferInstance
  have hp : IsPGroup 2 ((HStar F.H) ⧸ star F (K F)) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (residual_star (F := F)).symm)
  have hs := simple_two_quotient_structure (star F (K F))
    (Group.IsPerfect.not_isMulCommutative _) hp (pCore_quotient_pCore_eq_bot 2)
  have hz : center (star F (K F)) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  exact ⟨⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩,hz,hs.2.1⟩

include c in
/-- Both F.9.18 orbit ratios and its invariant alternative on the literal
original section in the G₂ branch, with no assumed orbit or recognition data. -/
theorem orbitInputs_from_original
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
      (Multiplicative.toAdd.surjective.comp c.onto)
    let P : Sylow 2 (HStar F.H) :=
      (T.subtype (F.invariant 1)).mapSurjective
        (QuotientGroup.mk'_surjective (pCore 2 F.H))
    OrbitInputs σ (pResidual 2 (HStar F.H)) P (pResidual_sup_sylow_eq_top P) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro a ha
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) a
    have hk := LocalReduction.section_action_kernel_eq_core_of_escape h structural hescape c
    exact (QuotientGroup.eq_one_iff _).mpr (hk ▸ ha)
  have hcomm := OriginalCore.g2_core_commutator h hab hcomponent faithful eK
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨path⟩ := LocalReduction.exists_criticalPath h hab hescape structural uniqueness
  obtain ⟨path,selection⟩ := LocalReduction.select_critical_orientation_of_nontrivial_star
    h structural path (G2Source.source_critical_star_ne_bot c h hab hcomponent eK hf hcomm structural path)
  have hplace := LocalReduction.critical_le_Q h structural path
  have hne := G2Source.source_critical_star_ne_bot c h hab hcomponent eK hf hcomm structural path
  let : IsElementaryAbelian 2 path.Uα := IsElementaryAbelian.map (MulAut.conj path.conjugator⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (path.Uα.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf (hplace.trans (Q_le_H F))
  let : IsElementaryAbelian 2 (star F path.Uα) := IsElementaryAbelian.map (starMap F)
  have hA : IsElementaryTwo (star F path.Uα) := ⟨hne,inferInstance⟩
  obtain ⟨hq,hZ,hcent⟩ := component_properties hcomponent eK
  let := hq
  let : (star F (K F)).Normal := residual_star (F := F) ▸ inferInstance
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  obtain ⟨hquad,hbound⟩ := G2Source.source_selected_critical_bound c h hab structural hf path selection
  obtain ⟨hd,hl,hm⟩ := G2Source.critical_linear_bounds c h path (LocalReduction.critical_le_Ri h structural path) selection
  let B := c.imageSpace (commutatorPreimage F.U path.Uα path.Zα)
  have hcrit : B ≤ fixedSpace σ (star F path.Uα) ∨
      ∃ S : Submodule (ZMod 2) W, IsAtom S ∧
        ∀ a ∈ star F path.Uα, ∀ v ∈ B, σ a v - v ∈ S := by
    by_cases hz : c.imageSpace path.Zα = ⊥
    · left
      intro v hv a
      have hh := hm a a.property v hv
      rw [hz] at hh
      exact sub_eq_zero.mp hh
    · right
      refine ⟨c.imageSpace path.Zα,Submodule.isAtom_iff_finrank_eq_one.mpr ?_,hm⟩
      have hn : Module.finrank (ZMod 2) (c.imageSpace path.Zα) ≠ 0 :=
        fun hh => hz (Submodule.finrank_eq_zero.mp hh)
      omega
  have hi := Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.whole_isIrrPlus_of_quadratic_actor
    σ (star F (K F)) hf hcent hZ e (G2Source.full_star_commutator c h)
    (star F path.Uα) hA hquad hbound B hcrit hd
  rw [residual_star] at hi
  exact Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.orbitInputs_of_whole_isIrrPlus
    σ (pResidual 2 (HStar F.H)) hf hi (star F path.Uα) hA hquad hbound _ _

/-- The original G₂ branch is excluded from the earlier structural and
faithful-family theorems, without core-commutator or orbit callbacks. -/
theorem source_not_g2_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G)) :
    ¬ G2Residual F := by
  rintro ⟨eK⟩
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hescape : ¬ F.H ≤ normalizer (L : Set G) := by
    have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) := hunique.symm ▸ Set.mem_singleton _
    exact hh.2.2
  apply G2Source.source_not_g2_residual h hab hunique hcomponent structural
    (OriginalCore.g2_core_commutator h hab hcomponent faithful eK) ?_ ⟨eK⟩
  intro σ c
  exact orbitInputs_from_original c h hab hescape hcomponent structural faithful eK

/-- The actual Data consumer now retains only the independent earlier-source
inputs and the alternating recognition branch owned by the Data constructor. -/
theorem exists_data_of_original_g2_exclusion
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) :=
  exists_data_of_source_branches d h hab hunique hcomponent h52
    (source_not_g2_residual h hab hunique hcomponent structural faithful) h40

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalG2
