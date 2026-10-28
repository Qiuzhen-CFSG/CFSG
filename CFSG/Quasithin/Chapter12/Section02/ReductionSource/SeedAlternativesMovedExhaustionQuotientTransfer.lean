module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionLocalFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionQuotientTransfer

/-!
# The original quotient offender reduces to the binary local action

The actual chosen seed and its moving Sylow conjugate are distinct simple
component types. Their exchanged sum W is irreducible for the literal LT
image. Under strict normalizer enlargement, the previously constructed
escaping conjugate is a same-type copy disjoint from W. It supplies a
nonzero component map into the literal quotient U/W. The two-group
quotient of LT then extends this to an injective LT-module map W -> U/W.

Fixed codimension cannot increase on this embedded W. The same starred
actor is faithful on both original sections, so its rank is unchanged in
each faithful image and a quotient offender is a local offender. The
corrected B.5.1 classification now leaves the marked natural-plus-dual
SL4(2) or SL5(2) action in every strict-enlargement case.

These binary actions can be FF. Their actual multiplicity and centralizer
exclusions, U = W and final Source325 assembly remain with qt-baumann-fsu.
The original hmany guard, central component image and all action coordinates
are retained. Source: Aschbacher--Smith D.3.9(1), D.3.13 and3.2.5,
printed pp.199--202,580; refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exchanged, distinct simple component types make the original local
Sylow orbit irreducible for its complete actor. -/
theorem normalizer_local_section_irreducible
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let S := D.normalizerLocalSection h.toHypothesis1221
    IsIrreducible S.toRepresentation := by
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
  let P := D.normalizerLocalActor
  let S : Subrepresentation (ρ.comp P.subtype) := D.normalizerLocalSection h.toHypothesis1221
  let σ : Representation (ZMod 2) P (internalSection U (componentOrbit V (T : Subgroup G))) := S.toRepresentation
  let S₂ := internalSylow T M U hn D.sylow_normalizes_component
  have hKS : P = K ⊔ (S₂ : Subgroup _) := D.normalizerLocalActor_eq_component_sup_sylow
  have hKP : K ≤ P := hKS ▸ le_sup_left
  have hSP : (S₂ : Subgroup _) ≤ P := hKS ▸ le_sup_right
  let Kp := K.subgroupOf P
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  let Ip : Subrepresentation (σ.comp Kp.subtype) := I'.compActors ek.toMonoidHom
  let Jp : Subrepresentation (σ.comp Kp.subtype) := J'.compActors ek.toMonoidHom
  have hip : IsIrreducible Ip.toRepresentation := by
    change IsIrreducible (I'.toRepresentation.comp ek.toMonoidHom)
    exact (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective _).mpr hi'
  have hjp : IsIrreducible Jp.toRepresentation := by
    change IsIrreducible (J'.toRepresentation.comp ek.toMonoidHom)
    exact (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective _).mpr hj'
  have hnep : ¬ Nonempty (Ip.toRepresentation.Equiv Jp.toRepresentation) := by
    rintro ⟨c⟩
    apply hne'
    refine ⟨Representation.Equiv.mk c.toLinearEquiv ?_⟩
    intro k
    obtain ⟨x,rfl⟩ := ek.surjective k
    exact c.isIntertwining' x
  have htS : j g ∈ S₂ := ⟨g,ht,rfl⟩
  let tp : P := ⟨j g,hSP htS⟩
  have hex : Ip.toSubmodule.map (σ tp) = Jp.toSubmodule := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      change ρ (j g) w.val ∈ J.toSubmodule
      rw [conjugateSubrepresentationOrderIso_toSubmodule]
      exact ⟨w.val,hw,rfl⟩
    · intro hv
      change v.val ∈ J.toSubmodule at hv
      rw [conjugateSubrepresentationOrderIso_toSubmodule] at hv
      obtain ⟨w,hw,he⟩ := hv
      exact ⟨⟨w,hIW hw⟩,hw,Subtype.ext he⟩
  exact irreducible_of_exchanged_pair σ Kp Ip Jp hip hjp hnep hspan' tp hex

/-- Under strict enlargement, the whole local Sylow orbit embeds in its
literal quotient, with the complete local actor retained. -/
theorem normalizer_local_quotient_embedding_of_strict
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hneU : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ i : S.toRepresentation.IntertwiningMap S.quotientRepresentation,
      Function.Injective i := by
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
  let g : M := ⟨t,D.sylow_normalizes_component ht⟩
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let J := conjugateSubrepresentationOrderIso ρ K (j g) I
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
  let P := D.normalizerLocalActor
  let S : Subrepresentation (ρ.comp P.subtype) := D.normalizerLocalSection h.toHypothesis1221
  let σ : Representation (ZMod 2) P (internalSection U (componentOrbit V (T : Subgroup G))) := S.toRepresentation
  let Q : Representation (ZMod 2) P (Additive U ⧸ S.toSubmodule) := S.quotientRepresentation
  let S₂ := internalSylow T M U hn D.sylow_normalizes_component
  have hKS : P = K ⊔ (S₂ : Subgroup _) := D.normalizerLocalActor_eq_component_sup_sylow
  have hKP : K ≤ P := hKS ▸ le_sup_left
  have hSP : (S₂ : Subgroup _) ≤ P := hKS ▸ le_sup_right
  let Kp := K.subgroupOf P
  let Sp : Sylow 2 P := S₂.subtype hSP
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  have hquot : IsPGroup 2 (P ⧸ Kp) := by
    apply quotient_isPGroup_of_sup_eq_top (Sp : Subgroup P) Kp Sp.isPGroup'
    change (S₂ : Subgroup _).subgroupOf P ⊔ K.subgroupOf P = ⊤
    rw [sup_comm,←subgroupOf_sup hKP hSP,←hKS,subgroupOf_self]
  let Ip : Subrepresentation (σ.comp Kp.subtype) :=
    ⟨I.toSubmodule.comap W.toSubmodule.subtype,fun k v hv => I.apply_mem_toSubmodule (ek k) hv⟩
  let Jp : Subrepresentation (σ.comp Kp.subtype) :=
    ⟨J.toSubmodule.comap W.toSubmodule.subtype,fun k v hv => J.apply_mem_toSubmodule (ek k) hv⟩
  let ei : Ip.toSubmodule ≃ₗ[ZMod 2] I.toSubmodule :=
    Submodule.comapSubtypeEquivOfLe hIW
  have hspan' : Ip.toSubmodule ⊔ Jp.toSubmodule = ⊤ := by
    apply top_unique
    intro v _
    have hv : v.val ∈ I.toSubmodule ⊔ J.toSubmodule := hspan.symm ▸ v.property
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    exact Submodule.mem_sup.mpr ⟨⟨x,hIW hx⟩,hx,⟨y,hJW hy⟩,hy,Subtype.ext hxy⟩
  have hd : Disjoint Ip.toSubmodule Jp.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hv hw
    change v.val ∈ J.toSubmodule at hw
    rw [hJ] at hw
    exact Subtype.ext (Additive.toMul.injective (Subtype.ext
      ((D.moved_conjugate_inf_eq_bot h.toHypothesis1221 hc ht hnt).le ⟨hv,hw⟩)))
  let cp : IsCompl Ip.toSubmodule Jp.toSubmodule := ⟨hd,codisjoint_iff.mpr hspan'⟩
  obtain ⟨r,hr,hrtype,hrdis,_⟩ :=
    D.exists_repeated_disjoint_conjugate_of_normalizerOrbit_ne h hmany hc hm hneU
  let r' : M := ⟨r,hr⟩
  let Vr := V.map (MulAut.conj r).toMonoidHom
  have hVrU : Vr ≤ U := le_iSup (fun x : M => V.map (MulAut.conj x.val).toMonoidHom) r'
  let : IsElementaryAbelian 2 Vr := IsElementaryAbelian.of_le hVrU
  have hLVr : L ≤ normalizer (Vr : Set G) := normalizes_conjugate D.normalizes r'
  let R := internalImageSubrepresentation hn hLVr
  obtain ⟨e,he⟩ := same_internalImageSubrepresentation hn hVU hVrU D.normalizes hLVr hrtype
  let f : Ip.toRepresentation.IntertwiningMap (Q.comp Kp.subtype) := {
    toLinearMap := S.toSubmodule.mkQ.comp
      (R.toSubmodule.subtype.comp (e.toLinearMap.comp ei.toLinearMap))
    isIntertwining' k := by
      ext v
      have hv := he (ek k) (ei v)
      exact congrArg (fun w : R.toSubmodule => S.toSubmodule.mkQ w.val) hv }
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toLinearMap).mpr
    intro v hv
    have hmem : (e (ei v)).val ∈ S.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hv
    have hz : (e (ei v)).val = 0 :=
      Additive.toMul.injective (Subtype.ext (hrdis.le ⟨(e (ei v)).property,hmem⟩))
    have hez : e (ei v) = 0 := Subtype.ext hz
    exact ei.map_eq_zero_iff.mp (e.map_eq_zero_iff.mp hez)
  have hiI : IsIrreducible I.toRepresentation := internalImageSubrepresentation_irreducible
    hn D.normalizes (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  let := hiI
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  let : Nontrivial Ip.toSubmodule := ei.surjective.nontrivial
  let : IsIrreducible σ := D.normalizer_local_section_irreducible h hmany hc hm
  exact embedding_of_two_quotient_of_summand Kp hquot σ Q Ip Jp cp f hfi



/-- The original quotient offender also offends on the literal local section.
Both action images retain the rank of the same component-faithful actor. -/
theorem normalizer_local_offender_of_quotient_offender
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
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥ →
      IsOffender (imageRepresentation S.quotientRepresentation)
        (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)) →
      IsOffender (imageRepresentation S.toRepresentation)
        (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn ρ K S A hAS hA hAC hoff
  obtain ⟨i,hi⟩ := D.normalizer_local_quotient_embedding_of_strict h hmany hc hm hne
  have hAP : A ≤ D.normalizerLocalActor := by
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact hAS.trans le_sup_right
  let B := A.subgroupOf D.normalizerLocalActor
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAP⟩
    intro hz
    apply hA.1.2.1.1
    change A.subgroupOf D.normalizerLocalActor = ⊥ at hz
    rw [←map_subgroupOf_eq_of_le hAP,hz,Subgroup.map_bot]
  obtain ⟨hfW,hfQ,hrW,hrQ,_⟩ :=
    D.normalizer_sections_of_faithful_component_actor h.toHypothesis1221 hc hne A hAS
      hA.1.2.1 ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
        (hA.1.2.2.2.le.trans hA.1.1)) hAC
  refine ⟨hB.actionSubgroup S.toRepresentation hfW,?_⟩
  rw [fixedCodim_actionSubgroup,hrW]
  have hb : fixedCodim S.toRepresentation B ≤ fixedCodim S.quotientRepresentation B := by
    simpa only [Subgroup.map_id] using fixedCodim_map_le_of_embedding
      S.quotientRepresentation S.toRepresentation (MonoidHom.id _) i.toLinearMap hi
      (fun g v => (LinearMap.congr_fun (i.isIntertwining' g) v).symm) B
  have hq := hoff.2
  rw [fixedCodim_actionSubgroup,hrQ] at hq
  exact hb.trans hq

/-- Every strict enlargement has the same component-faithful starred actor
as a local offender and the marked binary natural-plus-dual local action.
The quotient-offender alternative has been discharged. -/
theorem exists_normalizer_local_naturalDual_of_moved_of_many
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
      IsOffender (imageRepresentation S.toRepresentation)
        (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∧
      ∃ d : ℕ, (d = 4 ∨ d = 5) ∧
        IsNaturalPlusDual (D.normalizerLocalComponentAction h.toHypothesis1221) d := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn ρ K S
  obtain ⟨A,hAS,hA,hAC,hcase⟩ :=
    D.exists_normalizer_faithful_section_offender_of_moved_of_many h hmany hc hm hne
  have hoff : IsOffender (imageRepresentation S.toRepresentation)
      (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) :=
    hcase.elim id (D.normalizer_local_offender_of_quotient_offender h hmany hc hm hne A hAS hA hAC)
  exact ⟨A,hAS,hA,hAC,hoff,D.normalizer_local_naturalDual_of_ff h hmany hc hm ⟨_,hoff⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
