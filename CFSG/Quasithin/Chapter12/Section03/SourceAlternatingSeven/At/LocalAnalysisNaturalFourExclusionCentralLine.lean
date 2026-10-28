module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionCentralLine
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionResiduals

/-!
# LocalAnalysisNaturalFourExclusionCentralLine at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionCentralLine`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private abbrev pointComponent_at (_S : Setup T L V) (z : G) := L ⊓ centralizer ({z} : Set G)

private theorem faithful_projection_action_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (l : L) : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
  letI := S.chosen.actionCentralizer_normal
  change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
  rw [e.symm_apply_apply]
  rfl

private theorem pointVector_val_at (z : V) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
  congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)

private theorem chosenAction_val_at (l : L) (w : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l w)) : G) =
      l * (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ := by
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem fixes_point_iff_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) (l : L) :
    S.fourFaithfulAction e (S.fourFaithfulProjection e l) (S.fourPointVector z) = S.fourPointVector z ↔
      (l : G) ∈ centralizer ({(z : G)} : Set G) := by
  rw [S.faithful_projection_action_at]
  have hi : Function.Injective (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) :=
    Subtype.val_injective.comp (S.chosen.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  rw [← hi.eq_iff, S.chosenAction_val_at, S.pointVector_val_at,
    mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

private def pointActor_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) : S.pointComponent_at z →*
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e) (S.fourPointVector z) :=
  ((S.fourFaithfulProjection e).comp (inclusion inf_le_left)).codRestrict _ (fun l =>
    (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mpr
      ((S.fixes_point_iff_at e z ⟨l,l.property.1⟩).mpr l.property.2))

private theorem pointActor_surjective_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) : Function.Surjective (S.pointActor_at e z) := by
  letI := S.chosen.actionCentralizer_normal
  intro g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) (e.symm g)
  have hf : S.fourFaithfulProjection e l = g := by
    change e (QuotientGroup.mk' _ l) = g
    rw [hl,e.apply_symm_apply]
  have hc : (l : G) ∈ centralizer ({(z : G)} : Set G) := by
    apply (S.fixes_point_iff_at e z l).mp
    rw [hf]
    exact (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mp g.property
  exact ⟨⟨l,l.property,hc⟩,Subtype.ext hf⟩

private theorem pointVector_ne_zero_at {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  apply hz
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

private theorem component_residual_le_perfect_at {z : G} :
    (solvableResidual (S.pointComponent_at z)).map (S.pointComponent_at z).subtype ≤
      S.fourPointPerfect z := by
  have hj : S.pointComponent_at z ≤ S.fourPointModuleNormalizer z :=
    inf_le_inf_right _ S.chosen.normalizes
  have hs : solvableResidual (S.fourPointModuleNormalizer z) ≤
      pResidual 2 (S.fourPointModuleNormalizer z) := by
    apply le_sInf
    rintro N ⟨hn,hN⟩
    letI := hn
    letI : Group.IsNilpotent ((S.fourPointModuleNormalizer z) ⧸ N) := hN.isNilpotent
    exact solvableResidual_le_of_solvable_quotient N
  have hr := map_solvableResidual_eq_of_residual_le
    (pResidual 2 (S.fourPointModuleNormalizer z)) hs
  let he := (pResidual 2 (S.fourPointModuleNormalizer z)).equivMapOfInjective
    (S.fourPointModuleNormalizer z).subtype (S.fourPointModuleNormalizer z).subtype_injective
  have hm := map_solvableResidual_eq he.toMonoidHom he.surjective
  have heq : S.fourPointPerfect z =
      (solvableResidual (S.fourPointModuleNormalizer z)).map
        (S.fourPointModuleNormalizer z).subtype := by
    unfold fourPointPerfect fourPointResidual
    rw [← hm, map_map]
    have hc : ((pResidual 2 (S.fourPointModuleNormalizer z)).map
        (S.fourPointModuleNormalizer z).subtype).subtype.comp he.toMonoidHom =
        (S.fourPointModuleNormalizer z).subtype.comp
          (pResidual 2 (S.fourPointModuleNormalizer z)).subtype := by
      apply MonoidHom.ext
      intro x
      exact coe_equivMapOfInjective_apply (pResidual 2 (S.fourPointModuleNormalizer z))
        (S.fourPointModuleNormalizer z).subtype (S.fourPointModuleNormalizer z).subtype_injective x
    rw [hc, ← map_map, hr]
  rw [heq]
  exact map_solvableResidual_mono hj

theorem four_module_le_pointPerfect_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) : V ≤ S.fourPointPerfect z :=
  (S.four_pointPerfect_moved e hd hz hz1).le.trans
    (le_normalizer_iff_commutator_le_right.mp
      ((S.four_module_le_pointLocal hz).trans
        (S.four_pointLocal_normalizes_perfect_at structural hz hz1)))

theorem four_pointCore_section_sylow_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    Chapter1.IsSylowIn 2 (S.fourPointCore z) (S.fourPointSection z) := by
  have hTC : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp ((mem_omegaCenterIn_iff _ _).mp hzT).2.1) t ht)
  have hTM : (T : Subgroup G) ≤ S.fourPointLocal z :=
    le_inf S.chosen.sylow_normalizes_component hTC
  have hTK := hTM.trans (S.four_pointLocal_normalizes_perfect_at structural hz hz1)
  let K := S.fourPointPerfect z
  let eK := (solvableResidual (S.fourPointResidual z)).equivMapOfInjective
    (S.fourPointResidual z).subtype (S.fourPointResidual z).subtype_injective
  letI : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hperfect : IsPPerfect 2 K := by
    intro N hn hq
    letI := hn
    by_contra hne
    letI : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    letI : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    letI : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hs : Chapter1.IsSylowIn 2 (S.fourPointCore z)
      (ChapterA.Section04.twoSectionCentralizer K (normalizer (K : Set G))) :=
    ChapterA.Section04.sylow_core_sectionCentralizer T K hperfect hTK
  have hQT : S.fourPointCore z ≤ (T : Subgroup G) := by
    let P := T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)
    have hh := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) P
    simpa only [P, Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using hh
  have hQ := (Chapter1.isSylowIn_iff.mp hs).2.1
  apply hs.restrict
  · intro q hq
    exact ⟨hTC (hQT hq),(hQ hq).2⟩
  · intro y hy
    exact ⟨hy.2.1,hy.2⟩

theorem fourResidualData_of_local_structure_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (pushingUp : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourPointPerfect z)
      (S.fourPointCore z) V)
    (faithful : ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z))
    (local_member : S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z where
  pushingUp := pushingUp
  faithful := faithful
  local_member := local_member
  quotient := quotient
  moved := S.four_pointPerfect_moved e hd hz hz1
  section_sylow := S.four_pointCore_section_sylow_at structural hz hz1 hzT

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

