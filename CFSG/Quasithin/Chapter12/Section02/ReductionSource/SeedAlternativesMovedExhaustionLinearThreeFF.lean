module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionLinearThree
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThreeFF

/-!
# Excluding the local FF section in the odd-degree SL₃ branch

The moved Sylow pair supplies two disjoint natural SL₃ constituents on
W, nonisomorphic for the original component. Literal internal action
coordinates and B.4.9 therefore exclude FF for the component action on W.

For the original starred actor, the inner lift from the preceding module
agrees with its action on all of W. When the actor is faithful on the
component, this lift is injective, so the same offender would contradict
the component exclusion. The final application under hmany consequently
leaves a nontrivial component centralizer or an offender on U/W.

The quotient FF exclusion, the remaining component-support argument,
U = W and full Source325 assembly remain with qt-baumann-fsu. All groups,
Sylow subgroups, action images and quotients here are the original ones.
Source: Aschbacher--Smith B.4.9(2), D.3.9(1), D.3.13 and D.3.19,
printed pp.92--94,199--203.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual component action on W cannot be FF in the natural SL₃ row:
the moved Sylow pair has two distinct module types for this same actor. -/
theorem normalizer_component_local_not_ff_of_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (F : BinaryField)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ¬ IsFFModule (invariantSubspace ρ K (internalSection U (componentOrbit V (T : Subgroup G)))
      (D.normalizer_sylow_section_component_invariant h.toHypothesis1221)).toRepresentation := by
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
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221
    (Or.inl ⟨F,⟨e⟩⟩)
  let a : ActionEquiv I.toRepresentation (linearNatural F 3) :=
    ⟨a₀.groupEquiv.trans e.groupEquiv,a₀.linearEquiv.trans e.linearEquiv,by
      intro k v
      exact (congrArg e.linearEquiv (a₀.intertwines k v)).trans
        (e.intertwines (a₀.groupEquiv k) (a₀.linearEquiv v))⟩
  obtain ⟨_,t,ht,hnt,hpair⟩ := D.sylowMovedModel_of_moved_of_many h hmany hc hm
  have hdis := D.moved_conjugate_inf_eq_bot h.toHypothesis1221 hc ht hnt
  have hnot := D.moved_conjugate_not_sameModule ht hnt
  let g : M := ⟨t,D.sylow_normalizes_component ht⟩
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let J := conjugateSubrepresentationOrderIso ρ K (j g) I
  have hVU : V ≤ U := le_componentOrbit V M
  have hVtW : Vt ≤ componentOrbit V (T : Subgroup G) := by
    rw [hpair]
    exact le_sup_right
  have hWU : componentOrbit V (T : Subgroup G) ≤ U :=
    iSup_conjugates_le_of_le_normalizer V T U hVU (D.sylow_normalizes_component.trans hn)
  have hVtU := hVtW.trans hWU
  let : IsElementaryAbelian 2 Vt := IsElementaryAbelian.of_injective
    (inclusion hVtU) (inclusion_injective hVtU)
  have hJ : J.toSubmodule = internalSection U Vt := by
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact internalSection_map_action hn hVU g
  have hLVt : L ≤ normalizer (Vt : Set G) := normalizes_conjugate D.normalizes g
  have hJI : J = internalImageSubrepresentation hn hLVt :=
    Subrepresentation.toSubmodule_injective hJ
  have hd : Disjoint I.toSubmodule J.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hi hj
    rw [hJ] at hj
    have hz : v.toMul.val = 1 := hdis.le ⟨hi,hj⟩
    exact Additive.toMul.injective (Subtype.ext hz)
  have hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
    rintro ⟨c⟩
    rw [hJI] at c
    apply hnot
    apply sameConjugationModule_of_internal hn L.le_normalizer hVU hVtU D.normalizes hLVt
    refine ⟨c.toLinearEquiv,?_⟩
    intro l v
    exact LinearMap.congr_fun (c.isIntertwining' (j.subgroupMap (L.subgroupOf M) l)) v
  let W := invariantSubspace ρ K (internalSection U (componentOrbit V (T : Subgroup G)))
    (D.normalizer_sylow_section_component_invariant h.toHypothesis1221)
  exact no_ff_on_subspace_of_disjoint_natural_linearThree (ρ.comp K.subtype) I J W
    (fun _ hv => le_componentOrbit V T hv)
    (by intro v hv; change v ∈ J.toSubmodule at hv; rw [hJ] at hv; exact hVtW hv) hd F a
    (conjugate_linearThree_action ρ K I F a (j g)) hne

/-- A starred actor faithful on the component cannot offend on the actual
W section in the odd-degree SL₃ branch. Its inner lift preserves that
literal action, so B.4.9 applies to the same offender. -/
theorem normalizer_starred_local_not_offender_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
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
      ¬ IsOffender (imageRepresentation S.toRepresentation)
        (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  let S := D.normalizerLocalSection h.toHypothesis1221
  let W := invariantSubspace ρ K (internalSection U (componentOrbit V (T : Subgroup G)))
    (D.normalizer_sylow_section_component_invariant h.toHypothesis1221)
  dsimp only
  intro A hAS hA hAC hoff
  obtain ⟨_,_,⟨f,hfk,_,_,hw⟩,_,_⟩ :=
    D.normalizer_starred_inner_and_rank_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [hfk]
    apply bot_unique
    intro a ha
    exact Subtype.ext (hAC.le ⟨a.property,ha⟩)
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
  have hfaith := (D.normalizer_sections_of_faithful_component_actor h.toHypothesis1221 hc hne
    A hAS hA.1.2.1
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)) hAC).1
  have hb : IsOffender S.toRepresentation B := by
    refine ⟨hB,?_⟩
    have hh := hoff.2
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank S.toRepresentation B hfaith] at hh
    exact hh
  let b : B ≃* A := subgroupOfEquivOfLe hAP
  let g := f.comp b.toMonoidHom
  have hh := (hb.subgroupOf S.toRepresentation le_rfl).map_equivariant
    (S.toRepresentation.comp B.subtype) W.toRepresentation g (hfi.comp b.injective)
    (LinearEquiv.refl (ZMod 2) W.toSubmodule)
    (fun x v => Subtype.ext (hw (b x) v).symm)
  exact D.normalizer_component_local_not_ff_of_linearThree h hmany hc hm F e ⟨_,hh⟩
/-- Under the original standing guard, the odd-degree SL₃ branch has a
starred actor with a nontrivial component centralizer or an offender on
the literal quotient U/W. The W offender alternative is discharged. -/
theorem exists_normalizer_centralizer_or_quotient_offender_of_odd_linearThree_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      (A ⊓ centralizer (K : Set (internalActionImage M U hn)) ≠ ⊥ ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor))) := by
  classical
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
  refine ⟨A,hAS,hA,?_⟩
  by_cases hAC : A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥
  · right
    have hsections := (D.normalizer_sections_of_faithful_component_actor h.toHypothesis1221 hc hne
      A hAS hA.1.2.1
      ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)) hAC).2.2.2.2
    exact hsections.resolve_left
      (D.normalizer_starred_local_not_offender_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA hAC)
  · exact Or.inl hAC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
