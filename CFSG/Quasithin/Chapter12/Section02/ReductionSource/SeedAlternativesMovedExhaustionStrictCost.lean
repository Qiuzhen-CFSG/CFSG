module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionQuotientFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionStrictCost

/-!
# Exact local displacement for the original odd-degree SL₃ actor

The literal Sylow orbit W is the sum of the original seed and its moved
conjugate. They are disjoint natural constituents for the same component,
and their module types are distinct. The natural-plus-dual calculation
therefore makes any strict ratio below two have fixed codimension exactly 3m.

For the original starred actor, the inner lift agrees on W and preserves
its image rank. The previously proved nontrivial component centralizer and
D.3.19 supply the strict inequality whenever the actor moves the component.
We obtain both the strict rank inequality and the centralizer displacement
budget, and translate the cost back to the original ambient subgroup using
the literal full preimage of the actor.

D.3.18's component-movement premise, the remaining support/multiplicity
exclusions, U = W and unconditional Source325 assembly remain with
qt-baumann-fsu. The component-movement premise remains explicit in these applications.
Source: Aschbacher--Smith, D.3.19 and the final D.3.10 argument, pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- D.3.19's strict inequality determines the exact cost on the original
Sylow orbit, since its two constituents are natural and nonisomorphic. -/
theorem normalizer_component_local_cost_eq_of_linearThree_strict
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
    let W := invariantSubspace ρ K (internalSection U (componentOrbit V (T : Subgroup G)))
      (D.normalizer_sylow_section_component_invariant h.toHypothesis1221)
    ∀ B : Subgroup K, IsElementaryTwo B →
      fixedCodim W.toRepresentation B < 2 * rank B →
      fixedCodim W.toRepresentation B = 3 * F.degree := by
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
  have hspan : I.toSubmodule ⊔ J.toSubmodule = W.toSubmodule := by
    rw [hJ]
    change internalSection U V ⊔ internalSection U Vt =
      internalSection U (componentOrbit V (T : Subgroup G))
    rw [hpair,internalSection_sup U V Vt hVU hVtU]
  dsimp only
  intro B hB hs
  exact spanning_pair_linearThree_cost_eq_of_strict (ρ.comp K.subtype) I J W
    (fun _ hv => le_componentOrbit V T hv)
    (by intro v hv; change v ∈ J.toSubmodule at hv; rw [hJ] at hv; exact hVtW hv) hd hspan F a
    (conjugate_linearThree_action ρ K I F a (j g)) hne B hB hs

/-- The natural seed makes the same component faithful on the containing W. -/
private theorem component_faithful_on_local_of_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (F : BinaryField)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    Function.Injective (invariantSubspace ρ K
      (internalSection U (componentOrbit V (T : Subgroup G)))
      (D.normalizer_sylow_section_component_invariant h)).toRepresentation := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  let I := internalImageSubrepresentation hn D.normalizes
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h
    (Or.inl ⟨F,⟨e⟩⟩)
  let a : ActionEquiv I.toRepresentation (linearNatural F 3) :=
    ⟨a₀.groupEquiv.trans e.groupEquiv,a₀.linearEquiv.trans e.linearEquiv,by
      intro k v
      exact (congrArg e.linearEquiv (a₀.intertwines k v)).trans
        (e.intertwines (a₀.groupEquiv k) (a₀.linearEquiv v))⟩
  exact faithful_overmodule_of_linearThree (ρ.comp K.subtype) I _
    (fun _ hv => le_componentOrbit V T hv) F a

/-- Exact local cost and strict rank budget for a starred actor moving the component. -/
theorem normalizer_starred_local_cost_of_odd_linearThree
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
    let W := internalSection U (componentOrbit V (T : Subgroup G))
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ¬ A ≤ centralizer (K : Set (internalActionImage M U hn)) →
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) = 3 * F.degree ∧
        3 * F.degree + 2 * rank (A ⊓ centralizer (K : Set (internalActionImage M U hn))) <
          2 * rank A ∧
        fixedCodim ρ (A ⊓ centralizer (K : Set (internalActionImage M U hn))) + 3 * F.degree ≤
          2 * rank A := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  let W := internalSection U (componentOrbit V (T : Subgroup G))
  let hKW := D.normalizer_sylow_section_component_invariant h.toHypothesis1221
  dsimp only
  intro A hAS hA hnC
  have hAW : A ≤ subspaceStabilizer ρ W := hAS.trans
    (internalSylow_section_stable T M U (componentOrbit V (T : Subgroup G)) hn
      D.sylow_normalizes_component (le_normalizer_componentOrbit V T))
  have hAC := D.normalizer_starred_centralizer_ne_bot_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA
  obtain ⟨hR,hs⟩ := D.normalizer_starred_section_strict_of_component_centralizer
    h.toHypothesis1221 hc A hAS hA hAC hnC
  have hs' : fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) <
      2 * rank (restrictedSubgroup ρ W A) := by
    have hr : (rank (restrictedSubgroup ρ W A) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hR.1.rank_pos)
    have hh := (ENNReal.div_lt_iff (Or.inl hr) (Or.inl (by simp))).mp hs
    exact_mod_cast hh
  obtain ⟨_,_,⟨f,_,_,_,hw⟩,_,_⟩ :=
    D.normalizer_starred_inner_and_rank_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  have hb := inner_lift_restricted_rank_and_cost ρ W K A hKW hAW
    (D.component_faithful_on_local_of_linearThree h.toHypothesis1221 F e) f hw
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hB : IsElementaryTwo f.range :=
    ⟨fun hz => hR.1.1 (hb.2.2.mp hz),IsElementaryAbelian.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective⟩
  have heq := D.normalizer_component_local_cost_eq_of_linearThree_strict
    h hmany hc hm F e f.range hB (by rwa [hb.1,hb.2.1])
  rw [hb.2.1] at heq
  have hbudget := (fixedCodim_kernel_add_restricted_le ρ W A hAW).trans
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1))
  rw [(D.normalizer_sylow_seed_orbit_kernels h.toHypothesis1221 hc A hAS).2,heq] at hbudget
  refine ⟨heq,?_,hbudget⟩
  have hr := rank_subspaceKernel_add_image ρ W A hAW
    ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le hAS)
  rw [(D.normalizer_sylow_seed_orbit_kernels h.toHypothesis1221 hc A hAS).2] at hr
  rw [heq] at hs'
  omega

/-- The same cost in the original ambient group, using the full preimage of A. -/
theorem normalizer_starred_ambient_local_cost_of_odd_linearThree
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
    let W := componentOrbit V (T : Subgroup G)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ¬ A ≤ centralizer (K : Set (internalActionImage M U hn)) →
      rank W - rank (W ⊓ centralizer
        (((A.comap (internalHom M U hn)).map M.subtype : Subgroup G) : Set G)) = 3 * F.degree := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  dsimp only
  intro A hAS hA hnC
  have he := (D.normalizer_starred_local_cost_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA hnC).1
  have hWU : W ≤ U := iSup_conjugates_le_of_le_normalizer V T U
    (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)
  rwa [internalSection_fixedCodim M U W hn hWU A
    (hAS.trans (internalSylow_section_stable T M U W hn D.sylow_normalizes_component
      (le_normalizer_componentOrbit V T)))] at he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
