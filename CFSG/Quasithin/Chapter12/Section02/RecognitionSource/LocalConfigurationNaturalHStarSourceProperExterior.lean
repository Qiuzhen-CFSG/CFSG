module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperRows
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# The exterior-five H-star overcomponent is impossible

The ten-dimensional irreducible action is the exterior square with its
possible graph twist retained in the marking. Its self-normalizer extends
the actual Y-action to YT with a two-group kernel. The H-star image is then
a binary flag parabolic, which is solvable. Its two-group kernel would make
the original nonsolvable component solvable.

This transports the checked exterior model calculation from the terminal
application to the original H-star setting, without a terminal-point or
later classification hypothesis. Source: Aschbacher–Smith, 12.2.7, pp.797–798.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H X Y W : Subgroup G}

private theorem join_actor_of_self_normalizing
    {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]
    (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (σ : Representation (ZMod 2) A M) (hf : Function.Injective σ.asGroupHom)
    (hn : normalizer (σ.asGroupHom.range : Set (Module.End (ZMod 2) M)ˣ) = σ.asGroupHom.range)
    (model : ActionEquiv E.quotientAction σ) :
    ∃ a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* A,
      Function.Surjective a ∧ IsPGroup 2 a.ker := by
  let := E.elementary
  obtain ⟨e,f,he⟩ := E.conjugationModel_of_quotientAction model
  let c : Additive W ≃ₗ[ZMod 2] M :=
    f.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let J := Y ⊔ (T : Subgroup G)
  let τ : Representation (ZMod 2) J M :=
    c.conjRingEquiv.toMonoidHom.comp (chosenJoinAction E hT)
  have hres (y : Y) : τ.asGroupHom (inclusion (show Y ≤ J from le_sup_left) y) =
      σ.asGroupHom (e (QuotientGroup.mk' (pCore 2 Y) y)) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    let w := f.symm (Multiplicative.ofAdd v)
    have hh : f.symm (Multiplicative.ofAdd (σ (e (QuotientGroup.mk' (pCore 2 Y) y))
        (f w).toAdd)) =
        (chosenJoinAction E hT (inclusion le_sup_left y) (Additive.ofMul w)).toMul :=
      Subtype.ext (he y w)
    have hh' := congrArg (fun z : W => (f z).toAdd) hh
    simp only [f.apply_symm_apply, w] at hh'
    exact hh'.symm
  let C := Y.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer E.sylow_normalizes_component)
  have himg : C.map τ.asGroupHom = σ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨e (QuotientGroup.mk' (pCore 2 Y) ⟨y,hy⟩),(hres ⟨y,hy⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨q,rfl⟩ := e.surjective g
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
      exact ⟨inclusion le_sup_left y,y.property,hres y⟩
  have hnorm := C.le_normalizer_map τ.asGroupHom
  rw [normalizer_eq_top,himg,hn] at hnorm
  let β : J →* σ.asGroupHom.range := τ.asGroupHom.codRestrict _
    (fun x => hnorm ⟨x,mem_top x,rfl⟩)
  let b := MonoidHom.ofInjective hf
  let a := b.symm.toMonoidHom.comp β
  have ha (y : Y) : a (inclusion (show Y ≤ J from le_sup_left) y) =
      e (QuotientGroup.mk' (pCore 2 Y) y) := by
    apply hf
    exact (congrArg Subtype.val (b.apply_symm_apply (β _))).trans (hres y)
  refine ⟨a,?_,?_⟩
  · intro g
    obtain ⟨q,rfl⟩ := e.surjective g
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
    exact ⟨inclusion le_sup_left y,ha y⟩
  · have hg : C ⊔ (U : Subgroup J) = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
      change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
      rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
    apply a.kernel_isPGroup_of_normal_supplement C U U.isPGroup' hg
    let d : C ≃* Y := subgroupOfEquivOfLe le_sup_left
    have hk : (a.comp C.subtype).ker = (pCore 2 Y).comap d.toMonoidHom := by
      ext y
      change a (inclusion le_sup_left (d y)) = 1 ↔ d y ∈ pCore 2 Y
      rw [ha,e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (d y)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective d.toMonoidHom d.injective

/-- A full binary join action with two-group kernel contradicts the
original nonsolvable H-star component. -/
theorem HStarGeneratingComponent.not_binary_join_actor_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) {m : ℕ}
    (a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup (m+1))
    (hs : Function.Surjective a) (hk : IsPGroup 2 a.ker) : False := by
  let J := Y ⊔ (T : Subgroup G)
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hHJ : H ≤ J := by
    rw [← C.generates]
    exact sup_le_sup hXY le_rfl
  let B := H.subgroupOf J
  let c : B ≃* H := subgroupOfEquivOfLe hHJ
  have hUB : (U : Subgroup J) ≤ B := fun _ ht => hH.1.1.2 ht
  have hu := ((chosen_hstar_minimalParabolic_at h D structural hTI hH).1).map c.symm.mapSubgroup
  have heU : ((T.subtype hH.1.1.2 : Subgroup H)).map c.symm.toMonoidHom =
      (U : Subgroup J).subgroupOf B := by
    ext x
    rw [mem_map_equiv]
    rfl
  change Order.HasUniqueMaximalOver
    ((T.subtype hH.1.1.2 : Subgroup H).map c.symm.toMonoidHom)
    ((⊤ : Subgroup H).map c.symm.toMonoidHom) at hu
  rw [heU,map_top_of_surjective _ c.symm.surjective] at hu
  let : Group.IsSolvable B :=
    BinaryLinear.SylowFlagOvergroups.solvable_of_two_kernel_uniqueMaximal a hs hk U B hUB hu
  let : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective
  exact Chapter1.mem_L_not_isSolvable (C.exists_maximal_overcomponent hH).1
    (Group.isSolvable_of_isSolvable_injective (f := inclusion C.component.1)
      (inclusion_injective _))

/-- The actual exterior-five row cannot occur on an H-star overcomponent. -/
theorem HStarGeneratingComponent.not_exterior_five_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : (Y ⧸ pCore 2 Y) ≃* SL5TenDimensional.Group)
    (hd : Module.finrank (ZMod 2) E.space = 10)
    (hi : IsIrreducible E.quotientAction) : False := by
  let := hi
  obtain ⟨q,c,_,hc⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten E.quotientAction e hd
  let model : ActionEquiv E.quotientAction (SL5TenDimensional.exteriorAction 2) := ⟨q,c,hc⟩
  have hTW := ((structural Y hY).2.2 W E).1
  obtain ⟨a,ha,hk⟩ := join_actor_of_self_normalizing E hTW _
    (SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
    SL5TenDimensional.ExteriorNormalizer.normalizer_two model
  let b := (slEquivLinear 5).toMonoidHom.comp a
  apply C.not_binary_join_actor_at h D structural hTI hH hXY b
    ((slEquivLinear 5).surjective.comp ha)
  rw [MonoidHom.ker_comp_of_injective _ _ (slEquivLinear 5).injective]
  exact hk

/-- After the linear exclusions, every proper overcomponent has an
alternating-seven/eight central action or the alternating-seven four-space. -/
theorem HStarGeneratingComponent.proper_alternating_rows_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal
    (∃ n, (n = 7 ∨ n = 8) ∧ Nonempty (ActionEquiv E.faithfulCentralAction
      (alternatingNatural n))) ∨
    (Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) ∧
      Module.finrank (ZMod 2) E.space = 4) := by
  let := E.actionCentralizer_normal
  cases C.proper_rows_at h D structural modules hTI hH hXY hY E with
  | exterior e hd hi =>
    exact (C.not_exterior_five_overcomponent_at h D structural hTI hH hXY.le hY E e hd hi).elim
  | alternating n hn action => exact Or.inl ⟨n,hn,⟨action⟩⟩
  | sevenFour e hd => exact Or.inr ⟨⟨e⟩,hd⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
