module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSuzukiExchange
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLocalFF

/-!
# The remaining local FF action in the chosen-seed exhaustion argument

The literal LT image on W has trivial two-core, so a local offender gives
all six corrected B.5.1 clauses on its actual offender subgroup. The original
chosen seed and its moving Sylow conjugate give two distinct simple component
types spanning W. Their faithfulness, zero fixed space and full movement are
proved in the original coordinates.

B.5.1(3) then forces an actual natural-plus-dual action for SL₄(2) or SL₅(2).
Together with the preceding support exclusions, every strict enlargement
U > W gives this marked local model or the same actor offending on U/W.
These binary models can be FF modules; they are not excluded by classification
alone. The quotient offender, binary multiplicity and centralizer argument,
general U = W and final Source325 assembly remain with qt-baumann-fsu.

Source: Aschbacher--Smith B.5.1(3) and D.3.9(1), printed pp.99--103,199--200,
used in D.3.13 and 3.2.5, pp.202,580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal local section has trivial two-core and satisfies the complete
corrected B.5.1 conclusion whenever its faithful image is an FF module. -/
theorem normalizer_local_ff_classification
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let σ := (D.normalizerLocalSection h.toHypothesis1221).toRepresentation
    let C := actionSubgroup σ (K.subgroupOf D.normalizerLocalActor)
    pCore 2 (actionImage σ) = ⊥ ∧
      (IsFFModule (imageRepresentation σ) →
        C ≤ offenderSubgroup (imageRepresentation σ) ∧
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            ((imageRepresentation σ).comp (offenderSubgroup (imageRepresentation σ)).subtype)
            (C.subgroupOf (offenderSubgroup (imageRepresentation σ))))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn K σ C
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let P := D.normalizerLocalActor
  let S := internalSylow T M U hn D.sylow_normalizes_component
  have hKS : P = K ⊔ (S : Subgroup _) := D.normalizerLocalActor_eq_component_sup_sylow
  have hKP : K ≤ P := hKS ▸ le_sup_left
  have hSP : (S : Subgroup _) ≤ P := hKS ▸ le_sup_right
  let Kp := K.subgroupOf P
  let Sp : Sylow 2 P := S.subtype hSP
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  let : IsQuasisimple Kp := IsQuasisimple.of_mulEquiv ek.symm
  have hnK : ¬ Kp ≤ σ.ker := by
    intro hh
    apply D.normalizer_seed_not_fixed h.toHypothesis1221 hc
    intro v hv k
    let kp : Kp := ek.symm k
    have he : σ kp.val = 1 := hh kp.property
    exact congrArg Subtype.val (LinearMap.congr_fun he
      (⟨v,le_componentOrbit V T hv⟩ : (D.normalizerLocalSection h.toHypothesis1221).toSubmodule))
  have hfix : (Sp : Subgroup P) ⊓ centralizer (Kp : Set P) ≤ σ.ker := by
    intro a ha
    have hac : a.val ∈ centralizer (K : Set (internalActionImage M U hn)) := by
      apply mem_centralizer_iff.mpr
      intro k hk
      exact congrArg Subtype.val (mem_centralizer_iff.mp ha.2 ⟨k,hKP hk⟩ hk)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (D.normalizer_sylow_component_centralizer_fixes h.toHypothesis1221 hc).2
      v.property ⟨a.val,ha.1,hac⟩
  have hquot : IsPGroup 2 (P ⧸ Kp) := by
    apply quotient_isPGroup_of_sup_eq_top (Sp : Subgroup P) Kp Sp.isPGroup'
    change (S : Subgroup _).subgroupOf P ⊔ K.subgroupOf P = ⊤
    rw [sup_comm,←subgroupOf_sup hKP hSP,←hKS,subgroupOf_self]
  have hsq : IsSQTK KnownSimple.IsKnownSimple Kp := (IsSQTK.equiv ek).mpr
    (D.normalizer_action_component_sqtk h K
      ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩)
  exact ⟨local_section_image_twoCore_eq_bot σ Kp hnK Sp hfix,
    fun hff => local_section_ff_classification σ Kp hnK Sp hfix hquot hsq hff⟩


/-- The literal component action on W, inside the original normalizer orbit. -/
@[expose] def normalizerLocalComponentAction
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    Representation (ZMod 2) K (internalSection U (componentOrbit V (T : Subgroup G))) :=
  letI := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let K := (L.subgroupOf M).map (internalHom M U hn)
  (invariantSubspace (UniqueFactor.imageRepresentation M U hn) K
    (internalSection U (componentOrbit V (T : Subgroup G)))
    (D.normalizer_sylow_section_component_invariant h)).toRepresentation

private theorem faithful_of_actionEquiv
    {H₀ H₁ E₀ E₁ : Type*} [Group H₀] [Group H₁]
    [AddCommGroup E₀] [Module (ZMod 2) E₀]
    [AddCommGroup E₁] [Module (ZMod 2) E₁]
    (ρ₀ : Representation (ZMod 2) H₀ E₀) (ρ₁ : Representation (ZMod 2) H₁ E₁)
    (a : ActionEquiv ρ₀ ρ₁) (hf : Function.Injective ρ₁) :
    Function.Injective ρ₀ := by
  intro x y he
  apply a.groupEquiv.injective
  apply hf
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
  exact (a.intertwines x w).symm.trans
    ((congrArg a.linearEquiv (LinearMap.congr_fun he w)).trans (a.intertwines y w))

/-- The actual moved Sylow pair supplies two distinct simple types spanning
W, with faithful, fixed-free and fully moved component action. -/
theorem normalizer_local_component_pair
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let τ := D.normalizerLocalComponentAction h.toHypothesis1221
    Function.Injective τ ∧ fixedSpace τ ⊤ = ⊥ ∧ moved τ ⊤ = ⊤ ∧
      ∃ I J : Subrepresentation τ,
        Representation.IsIrreducible I.toRepresentation ∧ Representation.IsIrreducible J.toRepresentation ∧
        I.toSubmodule ⊔ J.toSubmodule = ⊤ ∧
        ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let j := internalHom M U hn
  let K := (L.subgroupOf M).map j
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance j
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let I := internalImageSubrepresentation hn D.normalizes
  obtain ⟨hmodel,t,ht,hnt,hpair⟩ := D.sylowMovedModel_of_moved_of_many h hmany hc hm
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221 hmodel
  have hi : IsIrreducible I.toRepresentation := internalImageSubrepresentation_irreducible
    hn D.normalizes (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  have hnot := D.moved_conjugate_not_sameModule ht hnt
  let g : M := ⟨t,D.sylow_normalizes_component ht⟩
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let J := conjugateSubrepresentationOrderIso ρ K (j g) I
  have hj : IsIrreducible J.toRepresentation :=
    (Homogeneous.normalTypeAction ρ K).conjugate_irreducible I hi (j g)
  have hVU : V ≤ U := le_componentOrbit V M
  have hVtW : Vt ≤ componentOrbit V (T : Subgroup G) := by rw [hpair]; exact le_sup_right
  have hWU : componentOrbit V (T : Subgroup G) ≤ U :=
    iSup_conjugates_le_of_le_normalizer V T U hVU (D.sylow_normalizes_component.trans hn)
  have hVtU := hVtW.trans hWU
  let : IsElementaryAbelian 2 Vt := IsElementaryAbelian.of_injective
    (inclusion hVtU) (inclusion_injective hVtU)
  have hJ : J.toSubmodule = internalSection U Vt := by
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact internalSection_map_action hn hVU g
  have hLVt : L ≤ normalizer (Vt : Set G) := normalizes_conjugate D.normalizes g
  have hJI : J = internalImageSubrepresentation hn hLVt := Subrepresentation.toSubmodule_injective hJ
  have hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
    rintro ⟨c⟩
    rw [hJI] at c
    apply hnot
    apply sameConjugationModule_of_internal hn L.le_normalizer hVU hVtU D.normalizes hLVt
    exact ⟨c.toLinearEquiv,fun l v =>
      LinearMap.congr_fun (c.isIntertwining' (j.subgroupMap (L.subgroupOf M) l)) v⟩
  let W := invariantSubspace ρ K (internalSection U (componentOrbit V (T : Subgroup G)))
    (D.normalizer_sylow_section_component_invariant h.toHypothesis1221)
  have hIW : I ≤ W := fun _ hv => le_componentOrbit V T hv
  have hJW : J ≤ W := by
    intro v hv
    change v ∈ J.toSubmodule at hv
    rw [hJ] at hv
    exact hVtW hv
  have hspan : I.toSubmodule ⊔ J.toSubmodule = W.toSubmodule := by
    rw [hJ]
    change internalSection U V ⊔ internalSection U Vt = internalSection U (componentOrbit V (T : Subgroup G))
    rw [hpair,internalSection_sup U V Vt hVU hVtU]
  let τ := D.normalizerLocalComponentAction h.toHypothesis1221
  let I' : Subrepresentation τ := sectionLower (ρ.comp K.subtype) I W
  let J' : Subrepresentation τ := sectionLower (ρ.comp K.subtype) J W
  let ei : I'.toRepresentation.Equiv I.toRepresentation :=
    .mk (sectionLowerEquiv _ hIW) (by intro k; rfl)
  let ej : J'.toRepresentation.Equiv J.toRepresentation :=
    .mk (sectionLowerEquiv _ hJW) (by intro k; rfl)
  have hi' : IsIrreducible I'.toRepresentation :=
    (RepEquiv.irreducible_euqiv (ρ := I'.toRepresentation) (σ := I.toRepresentation)
      ⟨ei.toLinearEquiv,ei.isIntertwining'⟩).mpr hi
  have hj' : IsIrreducible J'.toRepresentation :=
    (RepEquiv.irreducible_euqiv (ρ := J'.toRepresentation) (σ := J.toRepresentation)
      ⟨ej.toLinearEquiv,ej.isIntertwining'⟩).mpr hj
  have hne' : ¬ Nonempty (I'.toRepresentation.Equiv J'.toRepresentation) := by
    rintro ⟨c⟩
    exact hne ⟨ei.symm.trans (c.trans ej)⟩
  have hspan' : I'.toSubmodule ⊔ J'.toSubmodule = ⊤ := by
    apply top_unique
    intro v _
    have hv : v.val ∈ I.toSubmodule ⊔ J.toSubmodule := hspan.symm ▸ v.property
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    exact Submodule.mem_sup.mpr ⟨⟨x,hIW hx⟩,hx,⟨y,hJW hy⟩,hy,Subtype.ext hxy⟩
  have hz : fixedSpace τ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    apply (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc).le
    intro k
    exact congrArg Subtype.val (hv ⟨k,mem_top k⟩)
  have hfI : Function.Injective I.toRepresentation :=
    faithful_of_actionEquiv _ _ a₀
      ((subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective)
  have hfW : Function.Injective τ := by
    intro x y he
    apply hfI
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg
      (fun z : internalSection U (componentOrbit V (T : Subgroup G)) => (z : Additive U))
      (LinearMap.congr_fun he ⟨v.val,hIW v.property⟩)
  have hmove : moved τ ⊤ = ⊤ := by
    let e : (⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
    exact moved_eq_top_of_simple_pair τ ⊤
      (I'.compActors e.toMonoidHom) (J'.compActors e.toMonoidHom)
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr hi')
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr hj') hspan' hz
  exact ⟨hfW,hz,hmove,I',J',hi',hj',hspan',hne'⟩


/-- A local FF offender forces the actual W action to be natural plus dual
for SL₄(2) or SL₅(2). All other constituent rows are excluded here. -/
theorem normalizer_local_naturalDual_of_ff
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hff : letI := D.normalizerOrbit_elementary h.toHypothesis1221
      IsFFModule (imageRepresentation (D.normalizerLocalSection h.toHypothesis1221).toRepresentation)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    ∃ d : ℕ, (d = 4 ∨ d = 5) ∧
      IsNaturalPlusDual (D.normalizerLocalComponentAction h.toHypothesis1221) d := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let K := (L.subgroupOf M).map (internalHom M U hn)
  let σ : Representation (ZMod 2) D.normalizerLocalActor
      (internalSection U (componentOrbit V (T : Subgroup G))) :=
    (D.normalizerLocalSection h.toHypothesis1221).toRepresentation
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let P := D.normalizerLocalActor
  let S := internalSylow T M U hn D.sylow_normalizes_component
  have hKS : P = K ⊔ (S : Subgroup _) := D.normalizerLocalActor_eq_component_sup_sylow
  have hKP : K ≤ P := hKS ▸ le_sup_left
  have hSP : (S : Subgroup _) ≤ P := hKS ▸ le_sup_right
  let Kp := K.subgroupOf P
  let Sp : Sylow 2 P := S.subtype hSP
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  let : IsQuasisimple Kp := IsQuasisimple.of_mulEquiv ek.symm
  have hnK : ¬ Kp ≤ σ.ker := by
    intro hh
    apply D.normalizer_seed_not_fixed h.toHypothesis1221 hc
    intro v hv k
    let kp : Kp := ek.symm k
    have he : σ kp.val = 1 := hh kp.property
    exact congrArg Subtype.val (LinearMap.congr_fun he
      (⟨v,le_componentOrbit V T hv⟩ : (D.normalizerLocalSection h.toHypothesis1221).toSubmodule))
  have hfix : (Sp : Subgroup P) ⊓ centralizer (Kp : Set P) ≤ σ.ker := by
    intro a ha
    have hac : a.val ∈ centralizer (K : Set (internalActionImage M U hn)) := by
      apply mem_centralizer_iff.mpr
      intro k hk
      exact congrArg Subtype.val (mem_centralizer_iff.mp ha.2 ⟨k,hKP hk⟩ hk)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (D.normalizer_sylow_component_centralizer_fixes h.toHypothesis1221 hc).2
      v.property ⟨a.val,ha.1,hac⟩
  have hquot : IsPGroup 2 (P ⧸ Kp) := by
    apply quotient_isPGroup_of_sup_eq_top (Sp : Subgroup P) Kp Sp.isPGroup'
    change (S : Subgroup _).subgroupOf P ⊔ K.subgroupOf P = ⊤
    rw [sup_comm,←subgroupOf_sup hKP hSP,←hKS,subgroupOf_self]
  have hsq : IsSQTK KnownSimple.IsKnownSimple Kp := (IsSQTK.equiv ek).mpr
    (D.normalizer_action_component_sqtk h K
      ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩)
  let τ := D.normalizerLocalComponentAction h.toHypothesis1221
  obtain ⟨hf,hz,hmove,I,J,hi,hj,_,hne⟩ := D.normalizer_local_component_pair h hmany hc hm
  have hcomp : σ.comp Kp.subtype = τ.comp ek.toMonoidHom := rfl
  have hfaith : Function.Injective (σ.comp Kp.subtype) := by
    rw [hcomp]
    exact hf.comp ek.injective
  let I' : Subrepresentation (σ.comp Kp.subtype) := I.compActors ek.toMonoidHom
  let J' : Subrepresentation (σ.comp Kp.subtype) := J.compActors ek.toMonoidHom
  have hi' : IsIrreducible I'.toRepresentation := by
    change IsIrreducible (I.toRepresentation.comp ek.toMonoidHom)
    exact (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective I.toRepresentation).mpr hi
  have hj' : IsIrreducible J'.toRepresentation := by
    change IsIrreducible (J.toRepresentation.comp ek.toMonoidHom)
    exact (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective J.toRepresentation).mpr hj
  have hne' : ¬ Nonempty (I'.toRepresentation.Equiv J'.toRepresentation) := by
    rintro ⟨c⟩
    apply hne
    refine ⟨Representation.Equiv.mk c.toLinearEquiv ?_⟩
    intro k
    obtain ⟨x,rfl⟩ := ek.surjective k
    exact c.isIntertwining' x
  have hm' : moved σ Kp = ⊤ := by
    have he : subspaceCommutator (σ.comp Kp.subtype) ⊤ ⊤ =
        subspaceCommutator τ ⊤ ⊤ := by
      rw [hcomp,subspaceCommutator_comp_map,←MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr ek.surjective]
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype] at he
    exact he.trans hmove
  have hz' : fixedSpace σ Kp = ⊥ := by
    have he : fixedSpace (σ.comp Kp.subtype) ⊤ = fixedSpace τ ⊤ := by
      rw [hcomp,fixedSpace_comp_map,←MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr ek.surjective]
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,range_subtype] at he
    exact he.trans hz
  obtain ⟨d,hd,⟨a⟩⟩ := local_section_ff_naturalDual σ Kp hfaith Sp hfix hquot hsq hff
    hm' hz' I' J' hi' hj' hne'
  let b : ActionEquiv τ (σ.comp Kp.subtype) :=
    ⟨ek.symm,LinearEquiv.refl _ _,by
      intro k v
      change τ k v = τ (ek (ek.symm k)) v
      rw [ek.apply_symm_apply]⟩
  exact ⟨d,hd,⟨⟨b.groupEquiv.trans a.groupEquiv,b.linearEquiv.trans a.linearEquiv,
    fun g v => (congrArg a.linearEquiv (b.intertwines g v)).trans
      (a.intertwines (b.groupEquiv g) (b.linearEquiv v))⟩⟩⟩

/-- Every remaining strict enlargement either has the marked binary
natural-plus-dual local action, or the original actor offends on U/W. -/
theorem exists_normalizer_naturalDual_or_quotient_offender_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥ ∧
      ((∃ d : ℕ, (d = 4 ∨ d = 5) ∧
          IsNaturalPlusDual (D.normalizerLocalComponentAction h.toHypothesis1221) d) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn ρ K S
  obtain ⟨A,hAS,hA,hAC,hcase⟩ :=
    D.exists_normalizer_faithful_section_offender_of_moved_of_many h hmany hc hm hne
  refine ⟨A,hAS,hA,hAC,?_⟩
  exact hcase.imp
    (fun hoff => D.normalizer_local_naturalDual_of_ff h hmany hc hm ⟨_,hoff⟩) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
