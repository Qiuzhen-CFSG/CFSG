module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionBinaryCentralizer
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionBinaryRatio

/-!
# The original binary actor cannot act on three copies of the local pair

The two distinct simple component types in the actual Sylow orbit W force
its best-offender subgroup to equal its component image. The marked
natural-plus-dual model and Thompson replacement give a ratio strictly
greater than three quarters for every elementary actor in the faithful
local image. This retains the original actor's rank, rather than assuming
that a cubic actor is quadratic or already lies in the component.

In the strict-enlargement branch the existing source reduction supplies
that actor, its component faithfulness and its original two-rank budget.
Additivity of fixed codimensions therefore excludes three successive
LT-sections each equivalent to W. The full filtration, its resulting
multiplicity bound, the centralizer coordinates and U = W remain with
qt-baumann-fsu; this theorem does not assert those constructions exist.
All original component markings, local actions and hmany are retained.
Source: Aschbacher--Smith D.3.9(1), D.3.13 and3.2.5,
printed pp.199--202,580--581; refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
open scoped IsMulCommutative ENNReal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original local action on its literal section, with the vector
space displayed explicitly for subsequent faithful-image calculations. -/
@[expose] def normalizerLocalAction
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    Representation (ZMod 2) D.normalizerLocalActor
      (internalSection U (componentOrbit V (T : Subgroup G))) :=
  letI := D.normalizerOrbit_elementary h
  (D.normalizerLocalSection h).toRepresentation

/-- The best offenders on the literal local section generate exactly its
component image in the moved, FF branch. -/
theorem normalizer_local_offenderSubgroup_eq_component
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hff : letI := D.normalizerOrbit_elementary h.toHypothesis1221
      IsFFModule (imageRepresentation (D.normalizerLocalAction h.toHypothesis1221))) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
    let σ := (D.normalizerLocalAction h.toHypothesis1221)
    offenderSubgroup (imageRepresentation σ) = actionSubgroup σ (K.subgroupOf D.normalizerLocalActor) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let : AddCommGroup (Additive U) := inferInstance
  let : Module (ZMod 2) (Additive U) := inferInstance
  let : AddCommGroup (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let : Module (ZMod 2) (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
  let P := D.normalizerLocalActor
  let σ : Representation (ZMod 2) P (internalSection U (componentOrbit V (T : Subgroup G))) :=
    (D.normalizerLocalAction h.toHypothesis1221)
  have hKP : K ≤ P := by
    change K ≤ D.normalizerLocalActor
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact le_sup_left
  let Kp := K.subgroupOf P
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  let τ := D.normalizerLocalComponentAction h.toHypothesis1221
  obtain ⟨hf,hz,hmov,I,J,hi,hj,_,hne⟩ := D.normalizer_local_component_pair h hmany hc hm
  have hcomp : σ.comp Kp.subtype = τ.comp ek.toMonoidHom := rfl
  have hfaith : Function.Injective (σ.comp Kp.subtype) := by
    rw [hcomp]
    exact hf.comp ek.injective
  let a : ActionEquiv τ (σ.comp Kp.subtype) :=
    ⟨ek.symm,LinearEquiv.refl _ _,by
      intro k v
      change τ k v = τ (ek (ek.symm k)) v
      rw [ek.apply_symm_apply]⟩
  have hmove : moved σ Kp = ⊤ := by
    have he : subspaceCommutator (σ.comp Kp.subtype) ⊤ ⊤ =
        subspaceCommutator τ ⊤ ⊤ := by
      rw [hcomp,subspaceCommutator_comp_map,←MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr ek.surjective]
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype] at he
    exact he.trans hmov
  have hzero : fixedSpace σ Kp = ⊥ := by
    have he : fixedSpace (σ.comp Kp.subtype) ⊤ = fixedSpace τ ⊤ := by
      rw [hcomp,fixedSpace_comp_map,←MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr ek.surjective]
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,range_subtype] at he
    exact he.trans hz
  obtain ⟨hCJ,⟨c⟩⟩ := (D.normalizer_local_ff_classification h hc).2 hff
  exact image_offenderSubgroup_eq_of_source_distinct_types σ Kp hfaith hCJ c
    hmove hzero τ a I J hi hj hne

/-- Every elementary actor on the actual local faithful image has ratio
strictly greater than three quarters. Replacement retains the numerical
bound without assuming the given actor is quadratic. -/
theorem normalizer_local_actionRatio_gt_three_quarters
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hff : letI := D.normalizerOrbit_elementary h.toHypothesis1221
      IsFFModule (imageRepresentation (D.normalizerLocalAction h.toHypothesis1221))) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let σ := (D.normalizerLocalAction h.toHypothesis1221)
    ∀ A : Subgroup (actionImage σ), IsElementaryTwo A →
      (3 / 4 : ℝ≥0∞) < actionRatio (imageRepresentation σ) A := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let : AddCommGroup (Additive U) := inferInstance
  let : Module (ZMod 2) (Additive U) := inferInstance
  let : AddCommGroup (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let : Module (ZMod 2) (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
  let P := D.normalizerLocalActor
  let σ : Representation (ZMod 2) P (internalSection U (componentOrbit V (T : Subgroup G))) :=
    (D.normalizerLocalAction h.toHypothesis1221)
  change ∀ A : Subgroup (actionImage σ), IsElementaryTwo A →
    (3 / 4 : ℝ≥0∞) < actionRatio (imageRepresentation σ) A
  intro A hA
  have hKP : K ≤ P := by
    change K ≤ D.normalizerLocalActor
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact le_sup_left
  let Kp := K.subgroupOf P
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  let τ := D.normalizerLocalComponentAction h.toHypothesis1221
  let a : ActionEquiv τ (σ.comp Kp.subtype) :=
    ⟨ek.symm,LinearEquiv.refl _ _,by
      intro k v
      change τ k v = τ (ek (ek.symm k)) v
      rw [ek.apply_symm_apply]⟩
  obtain ⟨d,hd,hn⟩ := D.normalizer_local_naturalDual_of_ff h hmany hc hm hff
  exact image_actionRatio_gt_three_quarters_of_binary_chart σ Kp τ a
    (D.normalizer_local_component_pair h hmany hc hm).1
    (D.normalizer_local_offenderSubgroup_eq_component h hmany hc hm hff) hd hn A hA

set_option maxHeartbeats 400000 in
/-- In every remaining strict enlargement, three successive copies of
the actual LT-module W contradict the original starred actor's cubic budget.
Constructing the full filtration remains part of the multiplicity argument. -/
theorem normalizer_no_three_local_sections_of_strict
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∀ (X : Subrepresentation S.quotientRepresentation)
      (Y : Subrepresentation X.quotientRepresentation),
      ¬ (Nonempty (S.toRepresentation.Equiv X.toRepresentation) ∧
        Nonempty (S.toRepresentation.Equiv Y.toRepresentation)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let : AddCommGroup (Additive U) := inferInstance
  let : Module (ZMod 2) (Additive U) := inferInstance
  let : AddCommGroup (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let : Module (ZMod 2) (internalSection U (componentOrbit V (T : Subgroup G))) := inferInstance
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let P := D.normalizerLocalActor
  let S : Subrepresentation (ρ.comp P.subtype) := D.normalizerLocalSection h.toHypothesis1221
  change ∀ (X : Subrepresentation S.quotientRepresentation)
    (Y : Subrepresentation X.quotientRepresentation),
    ¬ (Nonempty (S.toRepresentation.Equiv X.toRepresentation) ∧
      Nonempty (S.toRepresentation.Equiv Y.toRepresentation))
  intro X Y
  obtain ⟨A,hAS,hA,hAC,hoff,_⟩ :=
    D.exists_normalizer_local_naturalDual_of_moved_of_many h hmany hc hm hne
  have hb : fixedCodim ρ A ≤ 2 * rank A :=
    (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  have hAP : A ≤ P := by
    change A ≤ D.normalizerLocalActor
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact hAS.trans le_sup_right
  let B := A.subgroupOf P
  have hrW : rank (actionSubgroup S.toRepresentation B) = rank A :=
    (D.normalizer_sections_of_faithful_component_actor
      h.toHypothesis1221 hc hne A hAS hA.1.2.1 hb hAC).2.2.1
  have hratio := D.normalizer_local_actionRatio_gt_three_quarters h hmany hc hm
    ⟨_,hoff⟩ (actionSubgroup S.toRepresentation B) hoff.1
  apply no_three_equivalent_sections_of_image_ratio (ρ.comp P.subtype) S B hoff.1
  · rw [rank_subgroupOf hAP]
    exact hrW
  · exact hratio
  · rw [fixedCodim_subgroupOf ρ hAP,rank_subgroupOf hAP]
    exact hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
