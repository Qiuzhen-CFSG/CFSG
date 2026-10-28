module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingComponent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceQuadratic

/-!
# Natural PSL₃(2) constituents detected by a minimal quadratic actor

For a stable homogeneous member of a semisimple component restriction,
D.2.5 gives quadratic ratio at most two in the faithful component-actor
image. Its generalized Fitting subgroup is the original centerless
component. Chapter K therefore supplies actual natural SL₃ coordinates
over a field of order two. All group and linear equivalences are pulled
back to the original component and invariant subspace.

Homogeneous selection preserving the central module type extends this
recognition to every prescribed noncentral irreducible component type.
The Chapter14 LinearThreeSections consumer constructs the actors and
semisimple restrictions on literal irreducible subquotients of U/Z.
Source: Aschbacher--Smith, D.2.5, p.179; D.3.6--7, pp.196--199;
B.4.5 and K.3.2, pp.87,455--456; F.9.18(5), pp.325--326.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Every noncentral irreducible component type has a literal binary natural marking. -/
@[expose] def NaturalLinearThreeTypes
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) : Prop :=
  ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I),
    ∃ F : BinaryField, F.degree = 1 ∧
      Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
        (linearNatural F 3))

/-- A stable homogeneous constituent detected by a minimal quadratic actor
has actual natural PSL₃(2) coordinates, on its original component action. -/
theorem stable_constituent_linear_three
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hm : ClassicalGroup.IsPSL K 3 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K C I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) :
    ∃ F : BinaryField, F.degree = 1 ∧
      Nonempty (ActionEquiv (invariantSubspace ρ K I hI.invariant).toRepresentation
        (linearNatural F 3)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨hD,hbound⟩ := ChapterD.stable_section_image_bound ρ hI
    (hI.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ) hZ hC hq hn
  let E := K ⊔ C
  let L := K.subgroupOf E
  let σ : Representation (ZMod 2) E I := (invariantSubspace ρ E I hD).toRepresentation
  let e : L ≃* K := subgroupOfEquivOfLe (show K ≤ E from le_sup_left)
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer (show K ≤ E from le_sup_left)).mpr
    (sup_le K.le_normalizer hI.normalizes)
  let : IsQuasisimple L := OriginalModule.Normal.componentInSup_quasisimple K C
  have hquot : IsPGroup 2 (E ⧸ L) := by
    let : IsElementaryAbelian 2 C := hC.1.1.2
    exact isPGroup_quotient_of_sup_eq_top L (C.subgroupOf E)
      (IsElementaryAbelian.isPGroup 2 C).comap_subtype (OriginalModule.Normal.componentInSup_generated K C)
  have hi : IsIrreducible (σ.comp L.subtype) := by
    have hir := hI.isIrrPlus.irreducible_of_semisimple ρ
    let τ := (invariantSubspace ρ K I hI.invariant).toRepresentation
    have heq : σ.comp L.subtype = τ.comp e.toMonoidHom := rfl
    rw [heq]
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective τ).mpr hir
  have hsurvive : ¬ L ≤ (actionHom σ).ker := by
    intro hh
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    intro v hv k
    exact congrArg Subtype.val ((actionHom_eq_one_iff σ (e.symm k)).mp
      (hh (e.symm k).property) (⟨v,hv⟩ : I))
  have hzL := OriginalModule.Normal.componentInSup_center K C hZ
  obtain ⟨hqs,hirr,hfit⟩ := image_structure σ L hsurvive hquot hi
  let j : K ≃* generalizedFitting (actionImage σ) :=
    e.symm.trans ((componentEquiv σ L hsurvive hzL).trans (MulEquiv.subgroupCongr hfit.symm))
  have hyp : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
      (imageRepresentation σ) (generalizedFitting (actionImage σ)) := by
    refine ⟨inferInstance,inferInstance,image_sqtk σ L hsurvive (hs.subgroup E) hquot hzL,
      rfl,?_,imageRepresentation_injective σ,?_,?_⟩
    · rw [hfit]; exact hqs
    · rw [hfit]; exact hirr
    · exact (cubicRatio_le_quadraticRatio _).trans hbound
  let zj : (generalizedFitting (actionImage σ) ⧸ center (generalizedFitting (actionImage σ))) ≃* K :=
    ((QuotientGroup.quotientMulEquivOfEq
      (RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.centerless_of_equiv hZ j)).trans
      QuotientGroup.quotientBot).trans j.symm
  have hm' : ClassicalGroup.IsPSL
      (generalizedFitting (actionImage σ) ⧸ center (generalizedFitting (actionImage σ)))
      3 (2 ^ 1) := by
    simpa only [pow_one] using hm.of_mulEquiv zj
  obtain ⟨F,hF,eQ,B,_⟩ := ChapterK.Linear.Recognition.SourceFF.exists_binaryField_cover hyp 1 (by decide) hm'
  obtain ⟨hnat⟩ := ChapterK.Linear.Recognition.SourceQuadratic.naturalSourceInput_of_quadratic_le_two
    hyp B eQ hbound
  refine ⟨F,hF,⟨⟨j.trans hnat.natural.groupEquiv,hnat.natural.linearEquiv,?_⟩⟩⟩
  intro k v
  exact hnat.natural.intertwines (j k) v

private def centralImageEquiv (ρ : Representation (ZMod 2) D V) (K : Subgroup D) (I : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ I) (hf : I ⊓ fixedSpace ρ K = ⊥) :
    (invariantSubspace ρ K I hs).toRepresentation ≃ₗ
      (quotientImage ρ K I hs).toRepresentation := by
  let q := (fixedSpace ρ K).mkQ
  let f : I →ₗ[ZMod 2] (quotientImage ρ K I hs).toSubmodule :=
    (q.comp I.subtype).codRestrict _ (fun v => ⟨v,v.property,rfl⟩)
  have hfi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hc : (v : V) - w ∈ fixedSpace ρ K := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change q ((v : V) - w) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val he)
    have hz : (v : V) - w ∈ I ⊓ fixedSpace ρ K :=
      ⟨I.sub_mem v.property w.property,hc⟩
    rwa [hf] at hz
  have hfs : Function.Surjective f := by
    rintro ⟨v,w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hfi,hfs⟩,?_⟩
  intro k
  ext v
  rfl

/-- Every prescribed noncentral irreducible component type is natural;
the selected homogeneous member is transported back to the original type. -/
theorem constituent_linear_three
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hm : ClassicalGroup.IsPSL K 3 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hCN : C ≤ normalizer (K : Set D))
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) :
    ∃ F : BinaryField, F.degree = 1 ∧
      Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
        (linearNatural F 3)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsElementaryAbelian 2 C := hC.1.1.2
  obtain ⟨J,_,hJ,htype⟩ := exists_isIrrPlusWith_le_orbitSpan_sameModule ρ hCN
    (IsElementaryAbelian.isPGroup 2 C) hI
  obtain ⟨F,hF,⟨a⟩⟩ := stable_constituent_linear_three ρ hZ hs hm hJ hC hq hn
  let e := ((centralImageEquiv ρ K I hI.choose
    (hI.inf_fixedSpace_eq_bot_of_semisimple ρ)).trans
      ((sameModule_iff_repEquiv _ _).mp htype).some).trans
        (centralImageEquiv ρ K J hJ.invariant
          (hJ.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ)).symm
  refine ⟨F,hF,⟨⟨a.groupEquiv,e.toLinearEquiv.trans a.linearEquiv,?_⟩⟩⟩
  intro k v
  exact (congrArg a.linearEquiv (LinearMap.congr_fun (e.isIntertwining' k) v)).trans
    (a.intertwines k (e v))

/-- The minimal actor recognizes all irreducible component types at once. -/
theorem naturalLinearThreeTypes_of_minimal_actor
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hm : ClassicalGroup.IsPSL K 3 2)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hCN : C ≤ normalizer (K : Set D))
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) : NaturalLinearThreeTypes ρ K := by
  intro I hI
  exact constituent_linear_three ρ (K := K) (C := C) hZ hs hm hI hCN hC hq hn

end CFSG.Quasithin.ChapterD
