module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceEqualExclusion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceExclusion
public import Theory.Representation.BinaryAlternatingSevenControl.NormalExtension
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceActionRows

/-!
# Excluding the binary A₇ four-space in an H-star overcomponent

Every chosen module of Y lies in O₂(H), since it is elementary, T-invariant
and normalized by H ≤ YT. Its relative centralizer in Y is solvable.
Minimal parabolicity and the proved movement of V therefore make V act
nontrivially on this module. On a faithful A₇ four-space the YT action is
inner, and a moving involution of V moves a plane. Since O₂(H) normalizes
V, the two independent moved points are actual elements of V. Their point
centralizers generate Y, contradicting NoEscape and the original residual's
escape from N_G(L).

The guarded source application now leaves only the six-dimensional
seven-point action, on the whole chosen module with its literal faithful
quotient. Excluding that remaining action and assembling solvability remain
with qt-d-12213-hstar-natural. No natural SL₂(4) TI-pair premise is used here.
The internal import reuses the existing join-action coordinates without
changing their public boundary.

Source: Aschbacher–Smith, 12.2.7(3ii) and 12.2.19, printed pp.797,801–802.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X Y W : Subgroup G}

private theorem chosen_faithful_kernel_solvable
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal;
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) :
    Group.IsSolvable ((centralizer (W : Set G)).subgroupOf Y) := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf := e.surjective.comp E.coreToFaithful_surjective
  have hk : f.ker = center (Y ⧸ pCore 2 Y) := by
    have hh := IsQuasisimple.comap_center_of_surjective f hf
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),MonoidHom.comap_bot] at hh
    exact hh
  have hc : (centralizer (W : Set G)).subgroupOf Y ≤ centralPreimage (pCore 2 Y) := by
    intro y hy
    change QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y)
    rw [←hk]
    change e (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Y) y) = 1
    have hyq : QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Y) y = 1 :=
      (QuotientGroup.eq_one_iff y).mpr hy
    rw [hyq,map_one]
  let := centralPreimage_pCore_isSolvable (G := Y) 2
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)

private theorem overcomponent_chosen_le_hstar_core
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) : W ≤ H.pCoreIn 2 := by
  let := E.elementary
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [←C.generates]
    exact sup_le (hXY.trans E.normalizes) (((structural Y hY).2.2 W E).1)
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
    (E.le_sylow.trans hH.1.1.2) hHW

private theorem overcomponent_chosen_not_centralizes_residual
    (C : HStarGeneratingComponent T L H X)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal;
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) :
    ¬ X ≤ centralizer (W : Set G) := by
  intro hc
  let := chosen_faithful_kernel_solvable hY E e
  let f : X →* (centralizer (W : Set G)).subgroupOf Y :=
    (inclusion hXY).codRestrict _ (fun x => hc x.property)
  have hi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : (centralizer (W : Set G)).subgroupOf Y => (z.val : G)) he)
  exact Chapter1.mem_L_not_isSolvable (C.exists_maximal_overcomponent hH).1
    (Group.isSolvable_of_isSolvable_injective hi)

private theorem overcomponent_chosen_movement
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal;
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7))
    (hm : ¬ V ≤ H.pCoreIn 2) (hr : X = (pResidual 2 H).map H.subtype) :
    ¬ V ≤ centralizer (W : Set G) := by
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [←C.generates]
    exact sup_le (hXY.trans E.normalizes) (((structural Y hY).2.2 W E).1)
  let A := (centralizer (W : Set G)).subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (hHW.trans (normalizer_le_normalizer_centralizer W))
  have hXA := overcomponent_chosen_not_centralizes_residual C hH hXY hY E e
  have hc : A ≤ ChapterB.minimalParabolicCore (T.subtype hH.1.1.2)
      (chosen_hstar_minimalParabolic_at h D structural hTI hH) := by
    apply ChapterB.minimalParabolic_normal_le_core_of_residual_not_le
    intro hx
    apply hXA
    rw [hr]
    rintro _ ⟨x,hx',rfl⟩
    exact hx hx'
  intro hv
  apply hm
  intro v hv'
  have ht : (⟨v,hH.1.1.2 (D.le_sylow hv')⟩ : H) ∈
      ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ⊓
        ChapterB.minimalParabolicCore _ (chosen_hstar_minimalParabolic_at h D structural hTI hH) :=
    ⟨D.le_sylow hv',hc (hv hv')⟩
  rw [ChapterB.minimalParabolic_sylow_inf_core] at ht
  exact mem_map_of_mem H.subtype ht


omit [Finite G] in
private theorem chosen_join_conjugation (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (g : (Y ⊔ (T : Subgroup G) : Subgroup G)) (z : E.space) :
    (E.spaceEquiv (Multiplicative.ofAdd (joinAction E hT g z)) : G) =
      (g : G) * (E.spaceEquiv (Multiplicative.ofAdd z) : G) * (g : G)⁻¹ := by
  let := E.elementary
  change (E.spaceEquiv (Multiplicative.ofAdd ((joinCoordinates E).symm
    (chosenJoinAction E hT g ((joinCoordinates E) z)))) : G) = _
  have hh := congrArg (fun a : Additive W => (a.toMul : G))
    ((joinCoordinates E).apply_symm_apply
      (chosenJoinAction E hT g ((joinCoordinates E) z)))
  exact hh.trans (chosenJoinAction_apply E hT g (E.spaceEquiv (Multiplicative.ofAdd z)))

private def chosen_faithful_section
    (E : ChosenModule T Y W) (hWY : W ≤ Y)
    (e : letI := E.actionCentralizer_normal;
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) :
    letI := E.actionCentralizer_normal;
    BinaryConjugationSection Y W ⊥
      ((E.faithfulAction.comp e.symm.toMonoidHom).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Y)))) := by
  let := E.actionCentralizer_normal
  refine ⟨hWY,bot_le,E.normalizes,E.spaceEquiv.symm.toMonoidHom,
    E.spaceEquiv.symm.surjective,?_,?_⟩
  · rw [E.spaceEquiv.symm.toMonoidHom.ker_eq_bot E.spaceEquiv.symm.injective,bot_subgroupOf]
  · intro y w
    change (E.spaceEquiv.symm _).toAdd = E.faithfulAction (e.symm (e _)) _
    rw [e.symm_apply_apply,E.faithfulAction_mk]
    apply Multiplicative.ofAdd.injective
    apply E.spaceEquiv.injective
    change E.spaceEquiv (E.spaceEquiv.symm _) = _
    rw [E.spaceEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [E.spaceEquiv_apply]
    have he := E.spaceEquiv_apply (E.spaceEquiv.symm w).toAdd
    change (E.spaceEquiv (E.spaceEquiv.symm w) : G) = _ at he
    rw [E.spaceEquiv.apply_symm_apply] at he
    change (y : G) * (w : G) * (y : G)⁻¹ =
      (y : G) * ((E.spaceEquiv.symm w).toAdd.val.toMul.val : G) * (y : G)⁻¹
    rw [←he]

/-- The four-dimensional row of a proper H-star overcomponent is impossible
on its original chosen module. -/
theorem HStarGeneratingComponent.not_four_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) (hd : Module.finrank (ZMod 2) E.space = 4) : False := by
  let := E.actionCentralizer_normal
  obtain ⟨⟨e⟩,_⟩ := C.proper_seven_rows_at h D structural modules hTI hH hXY hY E
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY.le hY
  have hr := C.eq_residual_of_normalized hTX
  obtain ⟨eX⟩ := C.five_of_overcomponent_at h D structural modules hTI hH hXY.le hY
  let eK : pResidual 2 H ≃* X :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hr.symm)
  let eR := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans eX
  have hm := chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH (fun _ => ⟨eR⟩))
  have hmove := overcomponent_chosen_movement C h D structural hTI hH hXY.le hY E e hm hr
  obtain ⟨v,hv,hvn⟩ := SetLike.not_le_iff_exists.mp hmove
  let J := Y ⊔ (T : Subgroup G)
  let K := Y.subgroupOf J
  let hT := ((structural Y hY).2.2 W E).1
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer (structural Y hY).1)
  let τ := joinAction E hT
  let ρ := E.faithfulAction.comp e.symm.toMonoidHom
  have hρ : Function.Injective ρ := E.faithfulAction_injective.comp e.symm.injective
  let f := e.toMonoidHom.comp (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Y))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let c : K ≃* Y := subgroupOfEquivOfLe le_sup_left
  let fK := f.comp c.toMonoidHom
  have he (k : K) : τ k = ρ (fK k) := by
    rw [joinAction_component]
    change E.chosenAction (c k) = E.faithfulAction (e.symm (e _))
    rw [e.symm_apply_apply,E.faithfulAction_mk]
    rfl
  let vJ : J := ⟨v,(show (T : Subgroup G) ≤ J from le_sup_right) (D.le_sylow hv)⟩
  have hv2 : vJ ^ 2 = 1 := by
    let := D.elementary
    exact Subtype.ext (show v ^ 2 = 1 from
      elemPow_eq_one_of_isElementaryAbelian v hv)
  have hvτ : τ vJ ≠ 1 := by
    intro heq
    apply hvn
    intro w hw
    obtain ⟨z,hz⟩ := E.spaceEquiv.surjective ⟨w,hw⟩
    have hh := chosen_join_conjugation E hT vJ z.toAdd
    change (E.spaceEquiv (Multiplicative.ofAdd (τ vJ z.toAdd)) : G) = _ at hh
    rw [heq,Module.End.one_apply] at hh
    have hzw : (E.spaceEquiv z : G) = w := congrArg Subtype.val hz
    change (E.spaceEquiv z : G) = v * (E.spaceEquiv z : G) * v⁻¹ at hh
    rw [hzw] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hrank := BinaryAlternatingSevenControl.displacement_finrank_of_normal_extension
    τ K ρ hρ hd fK (hf.comp c.surjective) he vJ hv2 hvτ
  let R := LinearMap.range (τ vJ - LinearMap.id)
  change Module.finrank (ZMod 2) R = 2 at hrank
  let b := Module.finBasis (ZMod 2) R
  let i : Fin (Module.finrank (ZMod 2) R) := ⟨0,by omega⟩
  let j : Fin (Module.finrank (ZMod 2) R) := ⟨1,by omega⟩
  let u : W := E.spaceEquiv (Multiplicative.ofAdd (b i).val)
  let w : W := E.spaceEquiv (Multiplicative.ofAdd (b j).val)
  have hzV (z : R) : (E.spaceEquiv (Multiplicative.ofAdd z.val) : G) ∈ V := by
    obtain ⟨a,ha⟩ := z.property
    have ha' : τ vJ a - a = z.val := ha
    rw [←ha']
    have hc := chosen_join_conjugation E hT vJ a
    have hWQ := overcomponent_chosen_le_hstar_core C structural hH hXY.le hY E
    have hQV : H.pCoreIn 2 ≤ normalizer (V : Set G) := by
      simpa using chosen_hstar_core_normalizes_conjugate_at h D structural hH 1
    have hcomm : ⁅V,W⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hWQ.trans hQV)
    have hm : ⁅v,(E.spaceEquiv (Multiplicative.ofAdd a) : G)⁆ ∈ V :=
      hcomm (commutator_mem_commutator hv (E.spaceEquiv (Multiplicative.ofAdd a)).property)
    have hh : (E.spaceEquiv (Multiplicative.ofAdd (τ vJ a - a)) : G) =
        ⁅v,(E.spaceEquiv (Multiplicative.ofAdd a) : G)⁆ := by
      change ((E.spaceEquiv (Multiplicative.ofAdd (τ vJ a) /
        Multiplicative.ofAdd a)) : G) = _
      rw [map_div, Subgroup.coe_div, div_eq_mul_inv]
      change (E.spaceEquiv (Multiplicative.ofAdd (τ vJ a)) : G) *
        (E.spaceEquiv (Multiplicative.ofAdd a) : G)⁻¹ = _
      rw [hc]
      rfl
    exact hh.symm ▸ hm
  have hu : u ≠ 1 := by
    intro hu
    have hh := (map_eq_one_iff E.spaceEquiv E.spaceEquiv.injective).mp hu
    exact b.ne_zero i (Subtype.ext hh)
  have hw : w ≠ 1 := by
    intro hw
    have hh := (map_eq_one_iff E.spaceEquiv E.spaceEquiv.injective).mp hw
    exact b.ne_zero j (Subtype.ext hh)
  have huw : u ≠ w := by
    intro heq
    have hb : b i = b j := Subtype.ext (E.spaceEquiv.injective heq)
    have hij := b.injective hb
    exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val hij)
  exact chosen_hstar_false_of_seven_section_at h structural hnone hH Y W
    (hr ▸ hXY.le) ρ hρ hd f hf
    (chosen_faithful_section E ((chosen_le_component_core_at hY E structural).trans (pCoreIn_le 2 Y)) e)
    u w (hzV (b i)) (hzV (b j)) hu hw huw


/-- Every original chosen module of a proper overcomponent now has the
marked six-dimensional seven-point action on the entire space. -/
theorem HStarGeneratingComponent.proper_seven_full_natural_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal;
    Nonempty (ChapterB.QuasisimpleSource.ActionEquiv E.faithfulAction
      (ChapterB.QuasisimpleSource.alternatingNatural 7)) ∧
      Module.finrank (ZMod 2) E.space = 6 := by
  let := E.actionCentralizer_normal
  obtain ⟨_,ha⟩ := C.proper_seven_rows_at h D structural modules hTI hH hXY hY E
  rcases ha with ha | hd
  · obtain ⟨a⟩ := ha
    obtain ⟨b⟩ := E.fullAction_of_odd_alternating_quotient (by decide) (by decide) a
    refine ⟨⟨b⟩,?_⟩
    calc
      Module.finrank (ZMod 2) E.space =
          Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7)) := b.linearEquiv.finrank_eq
      _ = 6 := by simpa using BinaryPermutation.finrank_natural_odd (Ω := Fin 7) (by decide)
  · exact (C.not_four_overcomponent_at h D structural modules hnone hTI hH hXY hY E hd).elim

/-- The original guarded nonsolvable H-star construction is reduced to the
six-dimensional A₇ action on every chosen module, with both original quotients. -/
theorem chosen_hstar_proper_seven_full_natural_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X < Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), letI := E.actionCentralizer_normal;
        (T : Subgroup G) ≤ normalizer (W : Set G) ∧
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv E.faithfulAction
          (ChapterB.QuasisimpleSource.alternatingNatural 7)) ∧
        Module.finrank (ZMod 2) E.space = 6 := by
  obtain ⟨X,Y,C,hr,hXY,hY,hX,hYq,hrows⟩ :=
    chosen_hstar_proper_seven_overcomponent_of_many_at h D structural modules hmany hnone hTI hH hs
  exact ⟨X,Y,C,hr,hXY,hY,hX,hYq,fun _ E => ⟨(hrows _ E).1,
    C.proper_seven_full_natural_at h D structural modules hnone hTI hH hXY hY E⟩⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
