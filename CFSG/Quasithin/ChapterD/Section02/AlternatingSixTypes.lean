module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingComponent
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.NativeSource
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeCentralTypes

/-!
# Natural A₆ constituents detected by a quadratic actor

D.2.5 bounds the faithful component-actor action on a stable irreducible
constituent. The native Chapter K degree theorem forces degree four, and
four-space recognition supplies actual A₆ and linear markings. Homogeneous
selection transfers the marking to each original noncentral constituent.
Source: Aschbacher--Smith D.2.5, K.1 and F.9.18(4), printed pp.179,452,325.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Every noncentral irreducible component type has a literal binary natural A₆ marking. -/
@[expose] def NaturalAlternatingSixTypes
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) : Prop :=
  ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I),
    Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
        (alternatingNatural 6))

/-- A stable homogeneous constituent detected by a minimal quadratic actor
has actual natural A₆ coordinates, on its original component action. -/
theorem stable_constituent_alternating_six
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (e6 : K ≃* alternatingGroup (Fin 6))
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K C I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) :
    Nonempty (ActionEquiv (invariantSubspace ρ K I hI.invariant).toRepresentation
        (alternatingNatural 6)) := by
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
  let j6 := j.symm.trans e6
  have hz : center (generalizedFitting (actionImage σ)) = ⊥ :=
    RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.centerless_of_equiv hZ j
  have hyp : ChapterK.Alternating.Input (imageRepresentation σ)
      KnownSimple.IsKnownSimple (generalizedFitting (actionImage σ)) := by
    refine ⟨image_sqtk σ L hsurvive (hs.subgroup E) hquot hzL,rfl,?_,
      imageRepresentation_injective σ,?_,(cubicRatio_le_quadraticRatio _).trans hbound,?_⟩
    · rw [hfit]; exact hqs
    · rw [hfit]; exact hirr
    · exact Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).trans j6⟩
  have hd := ChapterK.Alternating.sixDegree_native_source
    (imageRepresentation σ) KnownSimple.IsKnownSimple (generalizedFitting (actionImage σ)) hyp j6
  let τ := (invariantSubspace ρ K I hI.invariant).toRepresentation
  have hf : Function.Injective τ := by
    intro x y hxy
    apply j.injective
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hxy
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace
    (τ.comp e6.symm.toMonoidHom) (hf.comp e6.symm.injective) hd
  refine ⟨⟨e6.trans a.groupEquiv,a.linearEquiv,?_⟩⟩
  intro k v
  simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,MulEquiv.trans_apply]
    using a.intertwines (e6 k) v

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
theorem constituent_alternating_six
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (e6 : K ≃* alternatingGroup (Fin 6))
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hCN : C ≤ normalizer (K : Set D))
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) :
    Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
        (alternatingNatural 6)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsElementaryAbelian 2 C := hC.1.1.2
  obtain ⟨J,_,hJ,htype⟩ := exists_isIrrPlusWith_le_orbitSpan_sameModule ρ hCN
    (IsElementaryAbelian.isPGroup 2 C) hI
  obtain ⟨a⟩ := stable_constituent_alternating_six ρ hZ hs e6 hJ hC hq hn
  let e := ((centralImageEquiv ρ K I hI.choose
    (hI.inf_fixedSpace_eq_bot_of_semisimple ρ)).trans
      ((sameModule_iff_repEquiv _ _).mp htype).some).trans
        (centralImageEquiv ρ K J hJ.invariant
          (hJ.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ)).symm
  refine ⟨⟨a.groupEquiv,e.toLinearEquiv.trans a.linearEquiv,?_⟩⟩
  intro k v
  exact (congrArg a.linearEquiv (LinearMap.congr_fun (e.isIntertwining' k) v)).trans
    (a.intertwines k (e v))

/-- The minimal actor recognizes all irreducible component types at once. -/
theorem naturalAlternatingSixTypes_of_minimal_actor
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (e6 : K ≃* alternatingGroup (Fin 6))
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hCN : C ≤ normalizer (K : Set D))
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) : NaturalAlternatingSixTypes ρ K := by
  intro I hI
  exact constituent_alternating_six ρ (K := K) (C := C) hZ hs e6 hI hCN hC hq hn

private theorem detecting_minimal_actor (ρ : Representation (ZMod 2) D V) {K A : Subgroup D}
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A) (hf : A ⊓ centralizer (K : Set D) = ⊥) :
    ∃ C, C ≤ A ∧ ¬ C ≤ centralizer (K : Set D) ∧
      C ∈ RPlusBound ρ 2 ∧ IsQuadratic ρ C := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨C,hCA,hC⟩ := exists_RPlusBound_subgroup ρ hA.1
    ((actionRatio_le_nat_iff ρ hA.1 2).mpr hA.2.2)
  refine ⟨C,hCA,?_,hC,fun c hc d hd v => hA.2.1 c (hCA hc) d (hCA hd) v⟩
  intro hc
  exact hC.1.1.1 (le_bot_iff.mp ((le_inf hCA hc).trans_eq hf))

/-- A detecting quadratic actor recognizes every noncentral component type
on every irreducible subquotient, without semisimplicity of the original module. -/
theorem subquotient_alternating_six_of_detecting_actor
    (ρ : Representation (ZMod 2) D V) {K A : Subgroup D} [IsQuasisimple K]
    (hK : K.IsSubnormal) (hz : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (e6 : K ≃* alternatingGroup (Fin 6))
    (hAN : A ≤ normalizer (K : Set D))
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A) (hf : A ⊓ centralizer (K : Set D) = ⊥)
    (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation) :
    NaturalAlternatingSixTypes N.quotientRepresentation K := by
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := Module.Finite.of_finite
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K hK)
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection U.toRepresentation σ
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U hA.2.1)
  have hd : fixedCodim σ A ≤ 2 * rank A := by
    have hu := fixedCodim_subrepresentation_le ρ U A
    have hn := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    have ha := hA.2.2
    change fixedCodim N.quotientRepresentation A ≤ 2 * rank A
    omega
  obtain ⟨C,hCA,hnC,hC,hqC⟩ := detecting_minimal_actor σ ⟨hA.1,hq,hd⟩ hf
  exact naturalAlternatingSixTypes_of_minimal_actor σ hz hs e6 (hCA.trans hAN) hC hqC hnC


omit [Finite D] in
set_option backward.isDefEq.respectTransparency false in
/-- Recognition on ambient irreducible subquotients identifies the literal
central quotient of every original Irr⁺ support, retaining its fixed kernel. -/
theorem central_constituent_alternating_six_of_sections
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [Group.IsPerfect K]
    (hK : K.IsSubnormal)
    (hsections : ∀ (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation),
      IsIrreducible N.quotientRepresentation → NaturalAlternatingSixTypes N.quotientRepresentation K)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
      (alternatingNatural 6)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let τ := centralQuotientRepresentation ρ K I hI.choose
  have hs : QuadraticFourGroup.IsIrreducibleSection (ρ.comp K.subtype) τ :=
    ⟨hI.choose_spec.2, invariantSubspace ρ K I hI.choose,
      centralSubspace ρ K I hI.choose, ⟨Representation.Equiv.refl _⟩⟩
  obtain ⟨U, N, hi, hs⟩ :=
    QuadraticFourGroup.SectionReduction.exists_irreducible_section_occurrence ρ K.subtype τ hs
  let σ := N.quotientRepresentation
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := inferInstance
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K hK)
  obtain ⟨J, ⟨b⟩⟩ := hs.exists_equiv_subrepresentation
  have hirr : IsIrreducible J.toRepresentation :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv b)).mpr hI.choose_spec.2
  have hn : ¬ J.toSubmodule ≤ fixedSpace σ K := by
    intro hj
    have hf (k : K) (v : centralQuotient ρ K I) : τ k v = v := by
      obtain ⟨w, rfl⟩ := b.toLinearEquiv.surjective v
      have hw : J.toRepresentation k w = w := Subtype.ext (hj w.property k)
      exact (LinearMap.congr_fun (b.isIntertwining' k) w).symm.trans
        (congrArg b.toLinearEquiv hw)
    apply hI.not_le_fixedSpace ρ
    rw [← hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    have hh := hf ⟨k,hk⟩ (Submodule.Quotient.mk (⟨v,hv⟩ : I))
    have hz : ((fixedSpace ρ K).comap I.subtype).mkQ
        ((⟨ρ k v, (hI.choose hk v).2 hv⟩ : I) - ⟨v,hv⟩) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hh
    exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp hz
  have hJ : IsIrrPlus σ K J.toSubmodule := isIrrPlus_of_simple_noncentral σ K J hirr hn
  obtain ⟨a⟩ := hsections U N hi J.toSubmodule hJ
  refine ⟨⟨a.groupEquiv,b.symm.toLinearEquiv.trans a.linearEquiv,?_⟩⟩
  intro k v
  exact (congrArg a.linearEquiv (LinearMap.congr_fun (b.symm.isIntertwining' k) v)).trans
    (a.intertwines k (b.symm v))


/-- A detecting quadratic actor marks the original central quotient of every Irr⁺ seed. -/
theorem central_alternating_six_of_detecting_actor
    (ρ : Representation (ZMod 2) D V) {K A : Subgroup D} [IsQuasisimple K]
    (hK : K.IsSubnormal) (hz : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (e6 : K ≃* alternatingGroup (Fin 6))
    (hAN : A ≤ normalizer (K : Set D))
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A)
    (hf : A ⊓ centralizer (K : Set D) = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
      (alternatingNatural 6)) :=
  central_constituent_alternating_six_of_sections ρ K hK
    (fun U N hi => subquotient_alternating_six_of_detecting_actor ρ hK hz hs e6 hAN hA hf U N hi) hI

end CFSG.Quasithin.ChapterD
