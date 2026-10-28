module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Source
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# B.5.1 on the literal component orbit of the omega-center

The movement hypothesis of 11.3.1 and 3.1.8 give L = [L,J(T)]. The
B.2.14 reduced orbit U = ⟨Z^L⟩ has a faithful LT/C_LT(U) action. Its
restriction to L has kernel exactly O₂(L): reducedness kills the two-core,
and the original faithful chosen quotient detects every remaining actor.
Thus its component image is the original L/O₂(L), with the quotient map
and left conjugation formula retained.

The Thompson image consists of best offenders, so its commutator with L
puts this component inside the full offender subgroup. The proved B.5.1
classification applies there, using the actual SQTK two-core quotient.
The source adapter also transports the previously proved zero fixed space
and full movement to this same representation. It does not yet narrow the
classification to the single/doubled natural cases or prove the Cartan
dichotomy; those steps remain with qt-d-1222-shadow-common-action.

Source: Aschbacher--Smith, 11.3.7, printed p.773, using B.2.7, B.2.14,
B.5.1 and 3.1.8(3), printed pp.77--78,99--103,576.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original moving H forces the component Thompson commutator. -/
theorem source_component_thompson (s : Hypothesis1131At D S U₁ H) :
    L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let E := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hH : H ∈ Chapter3.HStar (T : Subgroup G) E.maximalLocal := by
    simpa only [E, Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using s.outside
  have hz : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro hc
    apply s.moves_omega_center
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [← omegaCenterIn_eq_omegaOneAmbient (T : Subgroup G)]
    intro z hz h hh
    obtain ⟨c,hc,rfl⟩ := hc hz
    exact congrArg H.subtype (mem_center_iff.mp hc ⟨h,hh⟩)
  have huniq := E.lemma_3_2_3_uniqueness hu
  have hj := (E.qrcHypotheses hu hH).thompson_moves_of_noncentral_omega
    S.source.simpleQTKE huniq.1 huniq.2.2 E.module_ne_bot hz
  have he := E.actor_eq_commutator_of_thompson_not_centralizes hu hj
  simpa only [D.localOrbit_eq] using he


include D S in
/-- The original chosen faithful quotient detects the kernel on the larger orbit. -/
theorem componentOmegaSpan_centralizer_eq_core
    (hVU : V ≤ componentOmegaSpan T L) :
    (centralizer (componentOmegaSpan T L : Set G)).subgroupOf L = pCore 2 L := by
  let J := L ⊔ (T : Subgroup G)
  let W := (componentOmegaSpan T L).subgroupOf J
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hc : L.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L J 2 le_sup_left
      (show (L.subgroupOf J).Normal from inferInstance).isSubnormal
  have hcentral : J.pCoreIn 2 ≤ centralizer (componentOmegaSpan T L : Set G) := by
    have hh := map_mono (f := J.subtype)
      (le_centralizer_iff.mp (componentOmegaSpan_reduced D S).le_centralizer_pCore)
    have hu : W.map J.subtype = componentOmegaSpan T L :=
      map_subgroupOf_eq_of_le ((componentOmegaSpan_le_sylow D S).trans le_sup_right)
    have hm := hh.trans (map_centralizer_le_centralizer_image (W : Set J) J.subtype)
    change J.pCoreIn 2 ≤ centralizer (W.map J.subtype : Set G) at hm
    rwa [hu] at hm
  apply le_antisymm
  · intro l hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply S.faithful
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      have hv : (v.val.toMul.val : G) ∈ V :=
        D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have ha : D.chosenAction l v = v := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ (hVU hv)).symm
      rw [map_one]
      change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
      rw [ha]
  · intro l hl
    exact hcentral (hc (mem_map_of_mem L.subtype hl))


/-- The literal centralizer quotient of LT acting on the omega orbit. -/
@[expose] def ComponentOmegaQuotient (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) : Type _ :=
  letI := (componentOmegaSpan_reduced D S).normal
  ChapterB.InternalThompsonAction.ActionQuotient
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))

instance (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    Group (ComponentOmegaQuotient D S) :=
  letI := (componentOmegaSpan_reduced D S).normal
  inferInstanceAs (Group (ChapterB.InternalThompsonAction.ActionQuotient
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))))

instance (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    Finite (ComponentOmegaQuotient D S) :=
  letI := (componentOmegaSpan_reduced D S).normal
  inferInstanceAs (Finite (ChapterB.InternalThompsonAction.ActionQuotient
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))))

/-- The entire original elementary orbit, viewed as a binary module inside LT. -/
@[expose] def ComponentOmegaSpace (D : Chapter12.Section02.ChosenModule T L V)
    (_S : D.NonbinaryNaturalInput) : Type _ :=
  Additive ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))

instance (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    AddCommGroup (ComponentOmegaSpace D S) :=
  letI := (componentOmegaSpan_reduced D S).elementary
  inferInstanceAs (AddCommGroup (Additive
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))))

instance (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    Module (ZMod 2) (ComponentOmegaSpace D S) :=
  letI := (componentOmegaSpan_reduced D S).elementary
  inferInstanceAs (Module (ZMod 2) (Additive
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))))

instance (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    Finite (ComponentOmegaSpace D S) := inferInstanceAs (Finite (Additive
      ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))))

/-- The original LT centralizer projection. -/
@[expose] def componentOmegaProjection (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) : ↥(L ⊔ (T : Subgroup G)) →* ComponentOmegaQuotient D S :=
  letI := (componentOmegaSpan_reduced D S).normal
  ChapterB.InternalThompsonAction.actionMk
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))

/-- Left conjugation on the whole omega orbit, with its actual kernel removed. -/
@[expose] def componentOmegaRepresentation (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) :
    Representation (ZMod 2) (ComponentOmegaQuotient D S) (ComponentOmegaSpace D S) :=
  letI := (componentOmegaSpan_reduced D S).normal
  letI := (componentOmegaSpan_reduced D S).elementary
  ChapterB.InternalThompsonAction.action
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))

/-- The image of the original L in the faithful orbit action. -/
@[expose] def componentOmegaActor (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) : Subgroup (ComponentOmegaQuotient D S) :=
  (L.subgroupOf (L ⊔ (T : Subgroup G))).map (componentOmegaProjection D S)

/-- Restriction of the centralizer projection to the original component. -/
@[expose] def componentOmegaActorMap (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) : L →* ComponentOmegaQuotient D S :=
  (componentOmegaProjection D S).comp (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))

/-- The restricted projection has precisely the original two-core kernel. -/
theorem componentOmegaActorMap_ker (hVU : V ≤ componentOmegaSpan T L) :
    (componentOmegaActorMap D S).ker = pCore 2 L := by
  let := (componentOmegaSpan_reduced D S).normal
  rw [← componentOmegaSpan_centralizer_eq_core (D := D) (S := S) hVU]
  ext l
  change (QuotientGroup.mk' (centralizer
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)) : Set ↥(L ⊔ (T : Subgroup G))))
    (inclusion le_sup_left l) = 1) ↔ _
  change inclusion le_sup_left l ∈ (QuotientGroup.mk' (centralizer
    ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)) : Set ↥(L ⊔ (T : Subgroup G))))).ker ↔ _
  rw [QuotientGroup.ker_mk']
  constructor
  · intro hl z hz
    exact congrArg Subtype.val (hl ⟨z,((componentOmegaSpan_le_sylow D S).trans le_sup_right hz)⟩ hz)
  · intro hl z hz
    exact Subtype.ext (hl z hz)

/-- The map and subgroup definitions describe the same component image. -/
theorem componentOmegaActorMap_range :
    (componentOmegaActorMap D S).range = componentOmegaActor D S := by
  rw [componentOmegaActorMap,MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩

/-- The faithful component image retains the literal two-core quotient. -/
@[expose] def componentOmegaActorEquiv (hVU : V ≤ componentOmegaSpan T L) :
    (L ⧸ pCore 2 L) ≃* componentOmegaActor D S :=
  ((QuotientGroup.quotientMulEquivOfEq (componentOmegaActorMap_ker (D := D) (S := S) hVU).symm).trans
    (QuotientGroup.quotientKerEquivRange (componentOmegaActorMap D S))).trans
      (MulEquiv.subgroupCongr componentOmegaActorMap_range)


/-- The component equivalence commutes with the original quotient projection. -/
theorem componentOmegaActorEquiv_mk (hVU : V ≤ componentOmegaSpan T L) (l : L) :
    (componentOmegaActorEquiv (D := D) (S := S) hVU
      (QuotientGroup.mk' (pCore 2 L) l) : ComponentOmegaQuotient D S) =
      componentOmegaActorMap D S l := rfl

/-- The centralizer quotient acts faithfully on the entire orbit. -/
theorem componentOmegaRepresentation_faithful :
    Function.Injective (componentOmegaRepresentation D S) := by
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  exact ChapterB.InternalThompsonAction.action_faithful _

/-- The marked action is literal left conjugation in G. -/
theorem componentOmegaRepresentation_apply
    (g : ↥(L ⊔ (T : Subgroup G))) (v : ComponentOmegaSpace D S) :
    (((componentOmegaRepresentation D S (componentOmegaProjection D S g) v).toMul.val) : G) =
      (g : G) * (v.toMul.val : G) * (g : G)⁻¹ := by
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  exact congrArg Subtype.val (ChapterB.InternalThompsonAction.action_apply _ g v)

open Representation.BinaryOffender ChapterB.InternalThompsonAction

/-- B.2.7 and Thompson generation put the original component in the offender actor. -/
theorem componentOmegaActor_le_offender
    (s : Hypothesis1131At D S U₁ H) :
    componentOmegaActor D S ≤ offenderSubgroup (componentOmegaRepresentation D S) := by
  let J := L ⊔ (T : Subgroup G)
  let W := (componentOmegaSpan T L).subgroupOf J
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let K := L.subgroupOf J
  have hK : K = ⁅K,Stellmacher.elementaryAbelianMaxJ (P : Subgroup J)⁆ := by
    apply map_injective J.subtype_injective
    rw [map_commutator, ← Stellmacher.elementaryAbelianMaxJ_map_injective
      J.subtype J.subtype_injective, map_subgroupOf_eq_of_le le_sup_left]
    change L = ⁅L,Stellmacher.elementaryAbelianMaxJ
      (((T : Subgroup G).subgroupOf J).map J.subtype)⁆
    rw [map_subgroupOf_eq_of_le le_sup_right]
    exact source_component_thompson s
  let := offenderSubgroup_normal (action W)
  change K.map (actionMk W) ≤ offenderSubgroup (action W)
  rw [hK,map_commutator]
  exact (commutator_mono le_rfl (thompson_image_le P W)).trans (commutator_le_right _ _)

/-- All six B.5.1 clauses on the original orbit; the source adapter below supplies V ≤ U. -/
theorem componentOmega_classification_of_seed
    (s : Hypothesis1131At D S U₁ H) (hVU : V ≤ componentOmegaSpan T L) :
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((componentOmegaRepresentation D S).comp
        (offenderSubgroup (componentOmegaRepresentation D S)).subtype)
      ((componentOmegaActor D S).subgroupOf
        (offenderSubgroup (componentOmegaRepresentation D S)))) := by
  let J := L ⊔ (T : Subgroup G)
  let W := (componentOmegaSpan T L).subgroupOf J
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  let Q := ActionQuotient W
  let q := actionMk W
  let ρ := action W
  let K := L.subgroupOf J
  let B := K.map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let e : (L ⧸ pCore 2 L) ≃* B := componentOmegaActorEquiv (D := D) (S := S) hVU
  let := S.source.quasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hgen : B ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤ := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self,
      map_top_of_surjective _ hq]
  have hquot : IsPGroup 2 (Q ⧸ B) := isPGroup_quotient_of_sup_eq_top B _
    ((T.isPGroup'.of_equiv (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).symm).map q) hgen
  have hsqL : IsSQTK KnownSimple.IsKnownSimple L := by
    let := D.elementary
    have hh : IsTwoLocal (normalizer (V : Set G)) :=
      ⟨V,D.ne_bot,IsElementaryAbelian.isPGroup 2 V,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe D.normalizes)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk hh).subgroup (L.subgroupOf (normalizer (V : Set G))))
  have hsqB : IsSQTK KnownSimple.IsKnownSimple B :=
    (IsSQTK.equiv e).mp (ChapterE.Structure.sqtk_two_quotient hsqL (pCore 2 L) pCore_isPGroup)
  have hBO : B ≤ offenderSubgroup ρ := componentOmegaActor_le_offender s
  have hff : IsFFModule ρ := by
    by_contra hn
    have hO : offenderSubgroup ρ = ⊥ := by
      apply bot_unique
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,_⟩
      exact (hn ((isFFModule_iff_exists_bestOffender ρ).mpr ⟨A,hA⟩)).elim
    have hb : B = ⊥ := bot_unique (hBO.trans hO.le)
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    have hnB : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot B).mp hnB hb
  exact (SourceCompletion.ff_quasisimple_source_conclusion ρ B hquot
    (componentOmegaSpan_reduced D S).quotient_pCore_eq_bot hsqB (action_faithful W) hff).2


/-- The group fixed-space conclusion is transported to the identical binary action. -/
theorem componentOmega_fixed_eq_bot
    (hc : componentOmegaSpan T L ⊓ centralizer (L : Set G) = ⊥) :
    fixedSpace (componentOmegaRepresentation D S) (componentOmegaActor D S) = ⊥ := by
  let J := L ⊔ (T : Subgroup G)
  let W := (componentOmegaSpan T L).subgroupOf J
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  apply bot_unique
  intro v hv
  have he := (NormalElementaryQuotient.mem_fixedSpace_image W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (L.subgroupOf J) v).mp hv
  have hcv : (v.toMul.val : G) ∈ centralizer (L : Set G) := by
    intro l hl
    exact congrArg Subtype.val (he ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)
  have hz : (v.toMul.val : G) = 1 := hc.le ⟨v.toMul.property,hcv⟩
  exact Subtype.ext (Subtype.ext hz)

/-- The literal commutator calculation makes this binary action fully moved. -/
theorem componentOmega_moved_eq_top
    (hm : componentOmegaSpan T L = ⁅omegaCenter T,L⁆) :
    subspaceCommutator (componentOmegaRepresentation D S) ⊤ (componentOmegaActor D S) = ⊤ := by
  let J := L ⊔ (T : Subgroup G)
  let W := (componentOmegaSpan T L).subgroupOf J
  let := (componentOmegaSpan_reduced D S).normal
  let := (componentOmegaSpan_reduced D S).elementary
  have he : ⁅W,L.subgroupOf J⁆ = W := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le
      ((componentOmegaSpan_le_sylow D S).trans le_sup_right),
      map_subgroupOf_eq_of_le le_sup_left, componentOmegaSpan_commutator D S,←hm]
  change subspaceCommutator (action W) ⊤ ((L.subgroupOf J).map (actionMk W)) = ⊤
  rw [action, ←NormalElementaryQuotient.commutatorSpace_eq W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)]
  apply top_unique
  intro v _
  change v.toMul.val ∈ ⁅W,L.subgroupOf J⁆
  rw [he]
  exact v.toMul.property

/-- Actual application of B.5.1 to the source orbit, with no classification,
Thompson, kernel, seed-containment, or fixed-space premise. The natural marking
and Hall containment are provided by the existing common-action assembly. -/
theorem source_component_module_classification
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    fixedSpace (componentOmegaRepresentation D S) (componentOmegaActor D S) = ⊥ ∧
    subspaceCommutator (componentOmegaRepresentation D S) ⊤ (componentOmegaActor D S) = ⊤ ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((componentOmegaRepresentation D S).comp
        (offenderSubgroup (componentOmegaRepresentation D S)).subtype)
      ((componentOmegaActor D S).subgroupOf
        (offenderSubgroup (componentOmegaRepresentation D S)))) := by
  obtain ⟨_,_,_,hVU,hm,hc⟩ := source_component_module s c A hA hHall hAL
  exact ⟨componentOmega_fixed_eq_bot hc,componentOmega_moved_eq_top hm,
    componentOmega_classification_of_seed s hVU⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
