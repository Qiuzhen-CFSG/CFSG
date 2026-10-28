module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic

/-!
# Fusion at the original ambient group and Sylow subgroup: Normalizer

These are ambient-local versions of the existing source fusion proofs. Only
the structural premise changes: each use is at the original G,T,L,V. The
literal module actions, quotient maps, point Sylow subgroups and conjugators
are preserved. The universal APIs remain available in their original modules.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800; the reducible
normalizer argument uses 3.3.1 and B.5.1 as in the original proofs.
-/

/- Adapted from FusionReducibleNormalizerBlockReductionEight. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

universe u

variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem thompson_moves_chosen_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  intro hc
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← chosen_sylow_centralizer_eq_core_at h D structural]
    exact le_inf (sSup_le fun _ hA => hA.1) hc
  have he := elementaryAbelianMaxJ_eq_of_intermediate_finite (T : Subgroup G) Q hJQ hQT
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hNJ := D.normal_subgroup_normalizer_le h.toHypothesis1221
    ((sSup_le fun _ hA => hA.1).trans (map_subtype_le _))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (pCore_isPGroup.map _) hQne)
    (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  apply hescape
  apply (normalizer_le_normalizer_elementaryAbelianMaxJ (T : Subgroup G)).trans
  rw [← he]
  exact hNJ

namespace EightReducedAction

private abbrev H_at (T : Sylow 2 G) (L : Subgroup G) := L ⊔ (T : Subgroup G)

private abbrev actor_at (T : Sylow 2 G) (L : Subgroup G) := (reducedConjugation (H_at T L)).range

private def projection_at : H_at T L →* actor_at T L := (reducedConjugation (H_at T L)).rangeRestrict

private theorem projection_surjective_at : Function.Surjective (projection_at (T := T) (L := L)) :=
  MonoidHom.rangeRestrict_surjective _

private abbrev representation_at : Representation (ZMod 2) (actor_at T L) (Additive (ReducedModule (H_at T L))) :=
  elementaryRepresentation (actor_at T L).subtype

local notation "ρ₀" => (representation_at (T := T) (L := L))

private theorem representation_projection_at (a : H_at T L) (w : Additive (ReducedModule (H_at T L))) :
    ρ₀ (projection_at a) w = reducedRepresentation (H_at T L) a w := rfl

private theorem projection_ker_at :
    (projection_at (T := T) (L := L)).ker = centralizer (ReducedModule (H_at T L) : Set (H_at T L)) := by
  ext a
  constructor
  · intro ha w hw
    have he := congrArg (fun f : MulAut (ReducedModule (H_at T L)) => (f ⟨w, hw⟩ : H_at T L))
      (congrArg Subtype.val (show projection_at a = 1 from ha))
    change a * w * a⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change a * (w : H_at T L) * a⁻¹ = w
    rw [← ha w w.property, mul_inv_cancel_right]

private abbrev component_at : Subgroup (actor_at T L) := (L.subgroupOf (H_at T L)).map projection_at

local notation "K₀" => (component_at (T := T) (L := L))

private def componentHom_at : L →* (component_at (T := T) (L := L)) :=
  (projection_at.subgroupMap (L.subgroupOf (H_at T L))).comp
    (subgroupOfEquivOfLe (show L ≤ H_at T L from le_sup_left)).symm.toMonoidHom

private theorem componentHom_surjective_at : Function.Surjective (componentHom_at (T := T) (L := L)) :=
  (projection_at.subgroupMap_surjective _).comp (subgroupOfEquivOfLe le_sup_left).symm.surjective

private theorem component_normal_at (D : ChosenModule T L V) : (component_at (T := T) (L := L)).Normal := by
  let : (L.subgroupOf (H_at T L)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact Normal.map inferInstance projection_at projection_surjective_at

private theorem chosen_irrPlus_at (D : ChosenModule T L V) :
    IsIrrPlus ρ₀ K₀ D.space := by
  apply D.irrPlus.isIrrPlus.of_intertwining (reducedRepresentation (H_at T L)) ρ₀
    (projection_at.subgroupMap (L.subgroupOf (H_at T L))) (projection_at.subgroupMap_surjective _)
    (LinearMap.id) Function.injective_id
  · intro l w
    rfl
  · exact Submodule.map_id _

private theorem component_ne_bot_at (D : ChosenModule T L V) : (component_at (T := T) (L := L)) ≠ ⊥ := by
  intro he
  apply (chosen_irrPlus_at D).not_le_fixedSpace ρ₀
  intro w hw k
  have hk : k.val = 1 := mem_bot.mp (he ▸ k.property)
  change ρ₀ k.val w = w
  rw [hk, map_one, Module.End.one_apply]

private theorem componentHom_core_at (D : ChosenModule T L V) :
    pCore 2 L ≤ (componentHom_at (T := T) (L := L)).ker := by
  intro l hl
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  change (l : G) * (w.val : G) * (l : G)⁻¹ = (w.val : G)
  have hcore : (l : G) ∈ (H_at T L).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component) (mem_map_of_mem L.subtype hl)
  have hc := (le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 (H_at T L)))
    (show (⟨l, (le_sup_left : L ≤ H_at T L) l.property⟩ : H_at T L) ∈ pCore 2 (H_at T L) from
      by
        obtain ⟨a, ha, he⟩ := hcore
        have he' : a = (⟨l, (le_sup_left : L ≤ H_at T L) l.property⟩ : H_at T L) := Subtype.ext he
        exact he' ▸ ha) w w.property
  have hc' : (w.val : G) * (l : G) = (l : G) * (w.val : G) :=
    congrArg (fun x : H_at T L => (x : G)) hc
  rw [← hc', mul_inv_cancel_right]

private def componentQuotientHom_at (D : ChosenModule T L V) :
    (L ⧸ pCore 2 L) →* (component_at (T := T) (L := L)) :=
  QuotientGroup.lift _ componentHom_at (componentHom_core_at D)

private theorem component_quasisimple_at (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) : IsQuasisimple (component_at (T := T) (L := L)) := by
  let := hq
  let : Nontrivial (component_at (T := T) (L := L)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (component_ne_bot_at D)
  exact IsQuasisimple.of_surjective (componentQuotientHom_at D)
    (QuotientGroup.lift_surjective_of_surjective _ componentHom_at componentHom_surjective_at (componentHom_core_at D))

private theorem quotient_two_at (D : ChosenModule T L V) : letI := component_normal_at D
    IsPGroup 2 (actor_at T L ⧸ (component_at (T := T) (L := L))) := by
  let X := L.subgroupOf (H_at T L)
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let := component_normal_at D
  have hp : IsPGroup 2 (H_at T L ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf (H_at T L))
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hx : X ≤ (K₀).comap projection_at := fun _ hx => mem_map_of_mem _ hx
  exact hp.of_surjective (QuotientGroup.map _ _ projection_at hx)
    (QuotientGroup.map_surjective_of_surjective _ _ projection_at
      ((QuotientGroup.mk'_surjective _).comp projection_surjective_at) hx)

private theorem actor_core_at : pCore 2 (actor_at T L) = ⊥ := by
  have hk : (reducedConjugation (H_at T L)).ker = centralizer (ReducedModule (H_at T L) : Set (H_at T L)) := by
    simpa only [projection_at, MonoidHom.ker_rangeRestrict] using (projection_ker_at (T := T) (L := L))
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange (reducedConjugation (H_at T L)))
  have hm := pCore_map_iso 2 e
  rw [isPReduced_reducedPSubgroup.quotient_pCore_eq_bot, Subgroup.map_bot] at hm
  exact hm.symm

private theorem component_sqtk_at [Finite G] (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (component_at (T := T) (L := L)) := by
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H_at T L from le_sup_left))).mp
      (h.join_sqtk.subgroup (L.subgroupOf (H_at T L)))
  let := component_quasisimple_at D h.quasisimple
  have hs : ChapterA.Section02.IsSemisimple (component_at (T := T) (L := L)) := by
    apply top_unique
    exact le_sSup (show IsComponent (component_at (T := T) (L := L)) ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  exact ⟨(show ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple L from
      ChapterA.Section02.theoremA_knownSimple).stronglyQuasithin_section
    hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective componentHom_at componentHom_surjective_at) hs,
    hL.isKGroup.of_surjective componentHom_at componentHom_surjective_at⟩

private theorem representation_injective_at : Function.Injective (representation_at (T := T) (L := L)) := by
  intro a b he
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (ReducedModule (H_at T L))) =>
    (f (Additive.ofMul w)).toMul) he

private theorem ff_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    IsFFModule (representation_at (T := T) (L := L)) := by
  let S : Sylow 2 (H_at T L) := T.subtype le_sup_right
  have hUS : ReducedModule (H_at T L) ≤ (S : Subgroup (H_at T L)) :=
    (reducedPSubgroup_le_pCore 2 _).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup (H_at T L)) ≤ projection_at.ker := by
    intro hj
    apply thompson_moves_chosen_at h D structural hescape
    have hm := map_mono hj (f := (H_at T L).subtype)
    rw [← elementaryAbelianMaxJ_map_injective (H_at T L).subtype (H_at T L).subtype_injective,
      show (S : Subgroup (H_at T L)).map (H_at T L).subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le le_sup_right] at hm
    intro a ha v hv
    obtain ⟨b, hb, he⟩ := hm ha
    rw [projection_ker_at] at hb
    obtain ⟨w, hw, hew⟩ := D.le_reduced hv
    rw [← he, ← hew]
    exact congrArg (fun x : H_at T L => (x : G)) (hb w hw)
  let σ := Representation.NormalElementaryQuotient.representation
    (ReducedModule (H_at T L)) projection_at projection_surjective_at projection_ker_at
  have hf : IsFFModule σ := Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (ReducedModule (H_at T L)) projection_at projection_surjective_at projection_ker_at S hUS hJS
  apply hf.map_equivariant σ ρ₀ (MonoidHom.id _) Function.injective_id (LinearEquiv.refl _ _)
  intro a w
  obtain ⟨g, rfl⟩ := projection_surjective_at a
  apply Additive.toMul.injective
  apply Subtype.ext
  exact Representation.NormalElementaryQuotient.representation_apply
    (ReducedModule (H_at T L)) projection_at projection_surjective_at projection_ker_at g w

private theorem source_conclusion_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    K₀ ≤ offenderSubgroup (representation_at (T := T) (L := L)) ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((ρ₀).comp (offenderSubgroup ρ₀).subtype)
      ((K₀).subgroupOf (offenderSubgroup ρ₀))) := by
  let := component_normal_at D
  let := component_quasisimple_at D h.quasisimple
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    ρ₀ K₀ (quotient_two_at D) actor_core_at (component_sqtk_at D h.toHypothesis1221)
    representation_injective_at (ff_at h D structural hescape)

private theorem mem_chosen_at (D : ChosenModule T L V)
    (w : Additive (ReducedModule (H_at T L))) : w ∈ D.space ↔ (w.toMul.val : G) ∈ V := by
  constructor
  · intro hw
    exact D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ hw))
  · intro hw
    obtain ⟨v, ⟨a, ha, rfl⟩, he⟩ := D.image_eq.ge hw
    have he' : Additive.ofMul a = w := Additive.toMul.injective (Subtype.ext (Subtype.ext he))
    exact he' ▸ ha

open ChapterB.QuasisimpleSource in

private theorem moved_not_compl_at (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ¬ IsCompl (moved ρ₀ K₀) (fixedSpace ρ₀ K₀) := by
  have hle : D.space ≤ moved ρ₀ K₀ := by
    rw [← (chosen_irrPlus_at D).choose_spec.1]
    exact subspaceCommutator_mono_left _ le_top _
  obtain ⟨⟨z, hz⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1 : z ≠ 1 := fun he => hz1' (Subtype.ext he)
  obtain ⟨w, hw, he⟩ := D.le_reduced hz.1
  have he' : (w : G) = z := he
  let v : Additive (ReducedModule (H_at T L)) := Additive.ofMul ⟨w, hw⟩
  have hv : v ∈ moved ρ₀ K₀ := hle ((mem_chosen_at D v).mpr (by
    change (w : G) ∈ V
    exact he'.symm ▸ hz.1))
  have hvfix : v ∈ fixedSpace ρ₀ K₀ := by
    intro k
    obtain ⟨l, rfl⟩ := componentHom_surjective_at k
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (w : G) * (l : G)⁻¹ = (w : G)
    rw [he', hz.2 l l.property, mul_inv_cancel_right]
  intro hc
  have hv0 : v = 0 := hc.disjoint.le_bot ⟨hv, hvfix⟩
  apply hz1
  exact he'.symm.trans (congrArg (fun x : Additive (ReducedModule (H_at T L)) => (x.toMul.val : G)) hv0)

open ChapterB.QuasisimpleSource in

private theorem moved_eq_chosen_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    moved ρ₀ K₀ = D.space := by
  obtain ⟨hKJ, ⟨c⟩⟩ := source_conclusion_at h D structural hescape
  have hspace : c.sectionData.space.toSubmodule = moved ρ₀ K₀ := by
    rw [c.sectionData.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hKJ]
  have hfix := fixedSpace_subgroupOf ρ₀ K₀ (offenderSubgroup ρ₀) hKJ
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace ((ρ₀).comp (offenderSubgroup ρ₀).subtype)
        ((K₀).subgroupOf (offenderSubgroup ρ₀))) := by
    rw [hspace, hfix]
    exact moved_not_compl_at D hne
  have hi := (IsIrrPlus.subgroupOf_iff ρ₀ K₀
    (offenderSubgroup ρ₀) hKJ c.sectionData.space.toSubmodule).mp (c.clause_two hn).1
  rw [hspace] at hi
  apply Eq.symm
  apply (chosen_irrPlus_at D).eq_of_le ρ₀ hi
  rw [← (chosen_irrPlus_at D).choose_spec.1]
  exact subspaceCommutator_mono_left _ le_top _

private theorem chosen_sylow_fixed_at [Finite G] (D : ChosenModule T L V)
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))
    (P : Sylow 2 L) (v : D.space) (hv : ∀ l ∈ (P : Subgroup L), D.chosenAction l v = v) :
    ∀ l : L, D.chosenAction l v = v := by
  let f : L →* alternatingGroup (Fin 8) :=
    E.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    E.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  let S := P.mapSurjective hf
  have hfixed : ∀ a ∈ (S : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.alternatingCoreRepresentation (Fin 8) a (E.linearEquiv v) = E.linearEquiv v := by
    rintro a ⟨l, hl, rfl⟩
    exact (E.intertwines (QuotientGroup.mk' (pCore 2 L) l) v).symm.trans
      (congrArg E.linearEquiv (hv l hl))
  have hc := BinaryPermutation.alternatingEight_core_sylow_fixed_constant S (E.linearEquiv v) hfixed
  have hall := (BinaryPermutation.core_fixed_iff_constant (Ω := Fin 8) (by simp) (E.linearEquiv v)).mpr hc
  intro l
  apply E.linearEquiv.injective
  exact (E.intertwines (QuotientGroup.mk' (pCore 2 L) l) v).trans (hall _)

private theorem exists_sylow_in_component_at [Finite G] (D : ChosenModule T L V) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let X := L.subgroupOf (H_at T L)
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let S : Sylow 2 (H_at T L) := T.subtype le_sup_right
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal X
  let e : X ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H_at T L)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro l ⟨r, hr, rfl⟩
  rw [hR] at hr
  exact hr

open ChapterB.QuasisimpleSource in

private theorem omega_centralizes_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (E : ActionEquiv D.quotientAction (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) := by
  let i : L →* H_at T L := inclusion (show L ≤ H_at T L from le_sup_left)
  let ρ := (reducedRepresentation (H_at T L)).comp i
  have hd : ∀ a z, ρ a z - z ∈ D.space := by
    intro a z
    rw [← moved_eq_chosen_at h D structural hne hescape]
    have he : ρ a z = ρ₀ ((componentHom_at (T := T) (L := L) a).val) z := rfl
    rw [he]
    exact Submodule.subset_span ⟨(componentHom_at (T := T) (L := L) a).val,
      (componentHom_at (T := T) (L := L) a).property, z, Submodule.mem_top, rfl⟩
  obtain ⟨P, hP⟩ := exists_sylow_in_component_at D
  let S : Sylow 2 (H_at T L) := T.subtype le_sup_right
  have hZU := sylow_omegaCenter_le_reduced S (join_characteristicTwo h)
  intro z hz
  have hzdata := (mem_omegaCenterIn_iff _ _).mp hz
  let zH : H_at T L := ⟨z, (le_sup_right : (T : Subgroup G) ≤ H_at T L) hzdata.1⟩
  have hzS : zH ∈ omegaCenterIn (S : Subgroup (H_at T L)) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzdata.1, ?_, ?_⟩
    · intro a ha
      exact Subtype.ext (hzdata.2.1 a ha)
    · exact Subtype.ext hzdata.2.2
  let y : Additive (ReducedModule (H_at T L)) := Additive.ofMul ⟨zH, hZU hzS⟩
  have hy : y ∈ fixedSpace ρ (P : Subgroup L) := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (a.val : G) * z * (a.val : G)⁻¹ = z
    rw [hzdata.2.1 a.val (hP a.val a.property), mul_inv_cancel_right]
  obtain ⟨w, hw, hyw⟩ := Representation.BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    ρ P D.space hd y hy
  let v : D.space := ⟨y-w, hyw⟩
  have hv : ∀ a ∈ (P : Subgroup L), D.chosenAction a v = v := by
    intro a ha
    apply Subtype.ext
    change ρ a (y-w) = y-w
    have hy' : ρ a y = y := hy ⟨a, ha⟩
    rw [map_sub, hy', hw a]
  have hvall := chosen_sylow_fixed_at D E P v hv
  have hyall (a : L) : ρ a y = y := by
    have hv' : ρ a (y-w) = y-w := congrArg Subtype.val (hvall a)
    rw [map_sub, hw a] at hv'
    exact sub_left_inj.mp hv'
  intro l hl
  have he := congrArg (fun x : Additive (ReducedModule (H_at T L)) => (x.toMul.val : G)) (hyall ⟨l, hl⟩)
  change l * z * l⁻¹ = z at he
  exact mul_inv_eq_iff_eq_mul.mp he

end EightReducedAction

public theorem reduced_commutator_le_chosen_of_escape_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ⁅(ReducedModule (L ⊔ (T : Subgroup G))).map
      (L ⊔ (T : Subgroup G)).subtype, L⁆ ≤ V := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro l hl _ ⟨w, hw, rfl⟩
  let v : Additive (ReducedModule (L ⊔ (T : Subgroup G))) := Additive.ofMul ⟨w, hw⟩
  let a := EightReducedAction.componentHom_at (T := T) (L := L) ⟨l, hl⟩
  have hm : EightReducedAction.representation_at a.val v - v ∈ D.space := by
    rw [← EightReducedAction.moved_eq_chosen_at h D structural hne hescape]
    exact Submodule.subset_span ⟨a.val, a.property, v, Submodule.mem_top, rfl⟩
  have hv := (EightReducedAction.mem_chosen_at D _).mp hm
  change l * (w : G) * l⁻¹ / (w : G) ∈ V at hv
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hv

public theorem sylow_normalizer_le_of_alternatingEight_core_at [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hc := EightReducedAction.omega_centralizes_at h D structural hne hescape E
  let Z := omegaCenterIn (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_sylow.trans_eq he))
  have hZne : Z ≠ ⊥ := by
    have hh := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
      (T : Subgroup G) (T : Subgroup G) le_rfl T.isPGroup' (T : Subgroup G).le_normalizer hTne
    exact fun he => hh (by rw [show omegaCenterIn (T : Subgroup G) = ⊥ from he, inf_bot_eq])
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hNZ : normalizer (T : Set G) ≤ normalizer (Z : Set G) := normalizer_le_normalizer_omegaCenterIn _
  exact hescape (hNZ.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hZT.trans le_sup_right) hZne (sup_le hLZ ((T : Subgroup G).le_normalizer.trans hNZ))))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end

/- Adapted from FusionReducibleNormalizerChosenControl. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem omegaCenter_split_chosen_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) =
      (V ⊓ omegaCenterIn (T : Subgroup G)) ⊔
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let Z := Stellmacher.omegaOneCenterAmbient (P : Subgroup H)
  let W := normalClosure (Z : Set H)
  let E := omegaCenterIn (T : Subgroup G)
  let F := E ⊓ centralizer (L : Set G)
  have hWR : blockOmegaModule T L ≤ (ReducedModule H).map H.subtype :=
    map_mono (omegaCenter_normalClosure_reduced P (join_characteristicTwo h)).le_reducedPSubgroup
  have hm : ⁅blockOmegaModule T L, H⁆ ≤ V := by
    rw [blockOmegaModule_commutator_join D]
    exact (commutator_mono hWR le_rfl).trans
      (reduced_commutator_le_chosen_of_escape_at h D structural hne hescape)
  have hc : (center H).map H.subtype ≤ centralizer (H : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hF : (W ⊓ center H).map H.subtype ≤ F := by
    rintro _ ⟨x,⟨hx,hxc⟩,rfl⟩
    have hxW : (x:G) ∈ blockOmegaModule T L := mem_map_of_mem _ hx
    have hxC := hc (mem_map_of_mem H.subtype hxc)
    refine ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨blockOmegaModule_le_sylow h hxW,
      centralizer_le (show (T : Subgroup G) ≤ H from le_sup_right) hxC, ?_⟩,
      centralizer_le (show L ≤ H from le_sup_left) hxC⟩
    let := blockOmegaModule_elementary h
    exact elemPow_eq_one_of_isElementaryAbelian (x:G) hxW
  have hW : blockOmegaModule T L ≤ V ⊔ F := by
    have hs := congrArg (Subgroup.map H.subtype)
      (omegaCenter_subgroup_normalClosure_split P (join_characteristicTwo h) Z le_rfl)
    rw [Subgroup.map_sup, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hs
    exact hs.le.trans (sup_le_sup hm hF)
  have hVF : V ≤ normalizer (F : Set G) := by
    apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact (show F ≤ centralizer (T : Set G) from fun _ hx =>
      ((mem_omegaCenterIn_iff _ _).mp hx.1).2.1).trans (centralizer_le D.le_sylow)
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
  intro z hz
  have hzW : z ∈ V ⊔ F := hW (omegaCenter_le_blockOmegaModule hz)
  have hzprod : z ∈ (V : Set G) * (F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V F hVF]
    exact hzW
  obtain ⟨v,hv,f,hf,rfl⟩ := hzprod
  have hvE : v ∈ E := by
    have he := E.mul_mem hz (E.inv_mem hf.1)
    simpa only [mul_inv_cancel_right] using he
  exact mul_mem_sup ⟨hv,hvE⟩ hf

public theorem sylow_normalizer_le_of_chosen_fixed_bounds_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hfixed : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2)
    (hsmall : Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 4) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let C := V ⊓ centralizer (L : Set G)
  obtain ⟨zi,hzi,hunique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hfixed
  let z : G := zi
  have hz : z ∈ C := zi.property
  have hz1 : z ≠ 1 := fun he => hzi (Subtype.ext he)
  have hfix : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hw hc
    by_cases he : w = 1
    · exact Or.inl he
    · exact Or.inr (congrArg Subtype.val (hunique ⟨w,hw,hc⟩
        (fun hh => he (congrArg Subtype.val hh))))
  by_contra hescape
  let E := omegaCenterIn (T : Subgroup G)
  let A := V ⊓ E
  let F := E ⊓ centralizer (L : Set G)
  have hzE : z ∈ E := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨D.le_sylow hz.1, ?_, ?_⟩
    · intro t ht
      exact (mem_centralizer_singleton_iff.mp
        (normalizer_centralizes_fixed_line_at h D structural hz.1 hz1 hz.2 hfix
          (D.sylow_normalizes_component ht)))
    · let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian z hz.1
  have hs : E = A ⊔ F := by
    have hne : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
      intro he
      rw [he, card_bot] at hfixed
      omega
    exact omegaCenter_split_chosen_at h D structural hne hescape
  have hAC : Nat.card (A ⊓ F : Subgroup G) = 2 := by
    have he : A ⊓ F = C := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · intro w hw
        rcases hfix w hw.1 hw.2 with rfl | rfl
        · exact one_mem _
        · exact ⟨⟨hz.1,hzE⟩,hzE,hz.2⟩
    exact he ▸ hfixed
  have hAsmall : Nat.card A ≤ 4 := (card_le_of_le (inf_le_inf_left V
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1))).trans hsmall
  obtain ⟨d,hd,hout⟩ := SetLike.not_le_iff_exists.mp hescape
  let f := (MulAut.conj d).toMonoidHom
  have hEd : E.map f = E := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G) hd)
  have hFd : F.map f ≤ E := (map_mono (show F ≤ E from inf_le_left)).trans hEd.le
  have hdis : F ⊓ F.map f = ⊥ := by
    apply bot_unique
    apply le_trans (inf_le_inf ?_ (map_mono ?_))
      (sylow_centralizer_disjoint_conjugate h D hd hout).le
    all_goals exact le_inf (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx.1).1) inf_le_right
  have hn (B J : Subgroup G) (hB : B ≤ E) (hJ : J ≤ E) : J ≤ normalizer (B : Set G) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro b hb j hj
    have hbT := ((mem_omegaCenterIn_iff _ _).mp (hB hb)).1
    exact (((mem_omegaCenterIn_iff _ _).mp (hJ hj)).2.1 b hbT).symm
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A F
    (hn A F inf_le_right inf_le_left)
  rw [hAC,←hs] at hprod
  have hFbound : Nat.card F * Nat.card F ≤ Nat.card E := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F (F.map f)
      (hn F (F.map f) inf_le_left hFd)
    rw [card_map_of_injective (MulAut.conj d).injective,hdis,card_bot,one_mul] at hc
    exact hc.le.trans (card_le_of_le (sup_le inf_le_left hFd))
  have hFsmall : Nat.card F ≤ 2 := by
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith
  have hFA : F ≤ A := by
    have he : A ⊓ F = F := eq_of_le_of_card_ge inf_le_right (hFsmall.trans_eq hAC.symm)
    exact he ▸ inf_le_left
  have hEV : E ≤ V := by rw [hs]; exact sup_le inf_le_left (hFA.trans inf_le_left)
  exact hescape (normalizer_le_of_fixed_line_in_omega_at h D structural hnone
    hz.1 hz1 hz.2 hfix (T : Subgroup G) hzE hEV)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end

/- Adapted from FusionReducibleNormalizerModelBounds. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open Representation.OneCohomology

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

open ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem sylow_normalizer_le_of_chosen_central_model_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) A W}
    (e : ActionEquiv D.centralQuotientAction σ)
    (hH : Module.finrank (ZMod 2) (H1 σ.dual) ≤ 1)
    (hS : ∀ P : Sylow 2 A, Nat.card (fixedSpace σ (P : Subgroup A)) ≤ 2) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  have hc := ChosenCover.fixed_card_eq_two D e hne hH
  exact sylow_normalizer_le_of_chosen_fixed_bounds_at h D structural hnone hc
    (ChosenCover.sylow_fixed_card_le_four D e hc hS)

public theorem sylow_normalizer_le_of_g2_central_model_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.centralQuotientAction (g2DerivedNatural (ZMod 2))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_chosen_central_model_at h D structural hnone hne e
    Atlas.G2.Natural.BinarySylowFixedSpace.derived_natural_dual_H1_finrank.le
    Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two

public theorem sylow_normalizer_le_of_g2_weyl_model_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.quotientAction (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let p := Atlas.G2.Natural.OrthogonalCover.projection (ZMod 2)
  have hp := Atlas.G2.Natural.OrthogonalCover.projection_isCover (ZMod 2)
  apply sylow_normalizer_le_of_g2_central_model_at h D structural hnone hne
  exact chosenCentralEquiv_of_cover D e p hp.1
    (by rw [Atlas.G2.Natural.OrthogonalCover.projection_ker,
      Atlas.G2.Natural.OrthogonalCover.fixed_eq_scalarLine])

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end

/- Adapted from FusionReducibleNormalizerBlockReductionLinearThree. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

open ChapterB.QuasisimpleSource Section04.SmallFusion

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem sylow_normalizer_le_of_slThree_extension_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (E : SLThreeExtension D) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  let e := chosenCentralEquiv_of_cover D (slThree_chosen_action_equiv D E)
    E.projection E.surjective E.kernel
  exact sylow_normalizer_le_of_chosen_central_model_at h D structural hnone hne e
    BinaryLinearThree.natural_dual_H1_finrank.le
    BinaryLinearThree.card_sylow_natural_fixed_le_two

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end

/- Adapted from FusionReducibleNormalizerBlockReductionRankTwo. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

open ChapterB.QuasisimpleSource BinaryPermutation

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem sylow_normalizer_le_of_alternatingSix_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_chosen_fixed_bounds_at h D structural hnone
    (six_core_fixed_card_eq_two D hne e)
    (chosen_sylow_fixed_card_le_of_faithful_model D e SixCoreSylow.card_fixed_le_four)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end

/- Adapted from FusionReducibleNormalizerComplete. -/
section
public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem sylow_normalizer_le_of_module_alternatives_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (rows : ModuleAlternatives1222 D) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  cases reducibleModels_of_module_alternatives h D hne rows with
  | linearThree E => exact sylow_normalizer_le_of_slThree_extension_at h D structural hnone hne E
  | alternatingSix E => exact sylow_normalizer_le_of_alternatingSix_core_at h D structural hnone hne E
  | g2 E => exact sylow_normalizer_le_of_g2_weyl_model_at h D structural hnone hne E
  | alternatingEight E => exact sylow_normalizer_le_of_alternatingEight_core_at h D structural hne E

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

end
end
