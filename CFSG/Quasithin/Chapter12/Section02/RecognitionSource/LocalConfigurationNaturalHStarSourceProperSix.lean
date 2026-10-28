module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperFour
public import Theory.Representation.BinaryPermutation.FiveMovedNormalTwo
public import Theory.Representation.AlternatingSevenFiveRestriction.DeletedMoved
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperFour
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceFiveExclusion
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceQuadratic
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceActionRows

/-!
# Excluding the deleted A₇ action in the original H-star configuration

The actual residual X=O²(H) has two-core quotient A₅. Its image on a chosen
six-dimensional deleted A₇ module is an A₅ normalized by the original full
Sylow, hence the pointwise stabilizer of two letters. The five-point core is
exactly its moved space. All quotient markings and conjugation coordinates
are retained when this summand is pulled back to the chosen module.

The normal two-core of H fixes this irreducible summand, so its marking
extends across X O₂(H). The original TI pair forces a Sylow four-group of
A₅ to act quadratically on it. The five-point core is not quadratic for any
such Sylow, giving the contradiction. This closes the remaining proper
overcomponent case without a natural SL₂(4) recognition premise.

Internal imports reuse the existing join coordinates, core-join projection
and TI-pair transport without changing their public boundaries.
Source: Aschbacher–Smith 12.2.7(3ii) and 12.2.19, printed pp.797–798,801–802;
the five-letter restriction is C.5.13, printed p.163.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X Y W : Subgroup G}

/-- The TI-pair obstruction detects a marked five-point summand, even when
the two-core acts nontrivially elsewhere on the section. -/
theorem chosen_hstar_no_five_embedded_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    (f : N →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N)
    (hm : ¬ V.subgroupOf N ≤ f.ker)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) N E)
    (S : Subgroup G) (hSQ : S ≤ H.pCoreIn 2)
    (C : BinaryConjugationSection N S ⊥ τ)
    (j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] E) (hj : Function.Injective j)
    (he : ∀ n v, j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (f n) v) = τ n (j v)) :
    False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  let : IsElementaryAbelian 2 ((V.subgroupOf N).map f) := IsElementaryAbelian.map _
  have hne : (V.subgroupOf N).map f ≠ ⊥ := fun he => hm ((Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨b,P,hP⟩ := Theory.SpecificGroups.Alternating.FiveConjugateSylow.exists_conjugate_generating_sylow
    ((V.subgroupOf N).map f) hne
  obtain ⟨g,hg⟩ := hf b
  let I := V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom
  have hi : (I.subgroupOf N).map f = (P : Subgroup _) := by
    change ((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f = _
    rw [pair_image N V hVN f g,hg,hP]
  have hp : IsPGroup 2 ((I.subgroupOf N).map f) := hi.symm ▸ P.isPGroup'
  have hc := chosen_hstar_pair_triple_commutator_at h D structural hTI hH N hNH hVN f hk g hp S hSQ
  have hq : IsQuadratic τ (I.subgroupOf N) := by
    have hh := BinaryConjugationSection.isQuadratic_of_triple_commutator_le
      N S ⊥ I τ (MonoidHom.id N) C hc.le
    simpa only [Subgroup.map_id] using hh
  apply BinaryPermutation.FiveQuadraticActors.sylow_not_quadratic P
  rw [←hi]
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  apply hj
  rw [he,map_sub,he]
  exact hq a ha b hb (j v)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X Y W : Subgroup G}

private theorem seven_five_embedding
    (hXY : X ≤ Y) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : ChosenModule T Y W)
    (a : letI := E.actionCentralizer_normal;
      ActionEquiv E.faithfulAction (alternatingNatural 7))
    (eX : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) :
    ∃ q : X →* alternatingGroup (Fin 5), Function.Surjective q ∧ q.ker = pCore 2 X ∧
    ∃ j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] E.space, Function.Injective j ∧
      (∀ x v, j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (q x) v) =
        E.chosenAction (inclusion hXY x) (j v)) ∧
      j.range = subspaceCommutator (E.chosenAction.comp (inclusion hXY)) ⊤ ⊤ := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  let π := a.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Y))
  have hπ : Function.Surjective π := a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkπ : π.ker ≤ centralPreimage (pCore 2 Y) := by
    let r := a.groupEquiv.toMonoidHom.comp E.coreToFaithful
    have hr := a.groupEquiv.surjective.comp E.coreToFaithful_surjective
    have hk : r.ker = center (Y ⧸ pCore 2 Y) := by
      have hh := IsQuasisimple.comap_center_of_surjective r hr
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),MonoidHom.comap_bot] at hh
      exact hh
    intro y hy
    change QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y)
    rw [←hk]
    exact hy
  let B0 := X.subgroupOf Y
  let d : B0 ≃* X := subgroupOfEquivOfLe hXY
  let e0 := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eX
  have hz : center (B0 ⧸ pCore 2 B0) = ⊥ := by
    apply bot_unique
    intro x hx
    apply e0.map_eq_one_iff.mp
    exact (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))).le
      (centerCongr e0 ⟨x,hx⟩).property
  have hk0 : IsPGroup 2 (π.subgroupMap B0).ker := by
    apply pCore_isPGroup.to_le
    rw [←centralPreimage_eq_of_center_quotient_eq_bot (pCore 2 B0) hz]
    intro x hx
    apply centralPreimage_pCore_comap_le 2 B0.subtype B0.subtype_injective
    apply hkπ
    exact congrArg Subtype.val hx
  let B := B0.map π
  let eB := alternatingGroup.SevenFiveSection.imageFiveEquiv π B0 hk0 e0
  have hker0 := (alternatingGroup.SevenFiveSection.image_twoCore_eq_bot_and_ker_eq π B0 hk0 e0).2
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le Y.le_normalizer (structural Y hY).1)
  have hU' : (U : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ Y := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup Y) ≤ (T : Subgroup G).subgroupOf Y := by
    intro x hx
    exact (show (x:G) ∈ (T : Subgroup G) ⊓ Y from hU' ▸ mem_map_of_mem Y.subtype hx).1
  have hUB : (U : Subgroup Y) ≤ normalizer (B0 : Set Y) :=
    (hUT.trans (comap_mono hTX)).trans (le_normalizer_comap Y.subtype)
  have hn : ((U.mapSurjective hπ : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup _) ≤
      normalizer (B : Set (alternatingGroup (Fin 7))) :=
    (map_mono hUB).trans (le_normalizer_map π)
  obtain ⟨e,j0,hj0,he0,hr0⟩ := BinaryPermutation.exists_five_core_moved_embedding B eB
    (U.mapSurjective hπ) hn
  let q0 := e.toMonoidHom.comp (π.subgroupMap B0)
  let q := q0.comp d.symm.toMonoidHom
  have hq : Function.Surjective q := e.surjective.comp
    ((π.subgroupMap_surjective B0).comp d.symm.surjective)
  have hkq : q.ker = pCore 2 X := by
    have hk0' : q0.ker = pCore 2 B0 :=
      (MonoidHom.ker_comp_of_injective _ _ e.injective).trans hker0
    ext x
    change d.symm x ∈ q0.ker ↔ x ∈ pCore 2 X
    rw [hk0',←pCore_map_iso 2 d]
    constructor
    · intro hx
      exact ⟨d.symm x,hx,d.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      change d.symm (d y) ∈ pCore 2 B0
      rw [d.symm_apply_apply]
      exact hy
  let F := a.linearEquiv.trans (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).symm
  let j := F.symm.toLinearMap.comp j0
  have hF (x : X) (v : E.space) :
      F (E.chosenAction (inclusion hXY x) v) =
        BinaryPermutation.coreRepresentation (Fin 7) (π (inclusion hXY x)).val (F v) := by
    apply (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).injective
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    simp only [F,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
    change a.linearEquiv (E.chosenAction (inclusion hXY x) v) =
      BinaryPermutation.naturalRepresentation (Fin 7) (π (inclusion hXY x)).val (a.linearEquiv v)
    simpa only [alternatingNatural,MonoidHom.comp_apply,π,MulEquiv.coe_toMonoidHom,Subgroup.coe_subtype,E.faithfulAction_mk] using a.intertwines (QuotientGroup.mk' _ (inclusion hXY x)) v
  refine ⟨q,hq,hkq,j,F.symm.injective.comp hj0,?_,?_⟩
  · intro x v
    apply F.injective
    change F (F.symm (j0 (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (q x) v))) = _
    rw [F.apply_symm_apply,hF]
    change j0 (BinaryPermutation.coreRepresentation (Fin 5) (e (π.subgroupMap B0 (d.symm x))).val v) =
      BinaryPermutation.coreRepresentation (Fin 7) (π (inclusion hXY x)).val
        (F (F.symm (j0 v)))
    rw [F.apply_symm_apply]
    exact he0 (π.subgroupMap B0 (d.symm x)) v
  · let πX := π.comp (inclusion hXY)
    have hi : (⊤ : Subgroup X).map πX = B := by
      ext b
      constructor
      · rintro ⟨x,_,rfl⟩
        exact ⟨inclusion hXY x,x.property,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,mem_top _,rfl⟩
    have hm := subspaceCommutator_map_embedding
      (E.chosenAction.comp (inclusion hXY))
      (BinaryPermutation.alternatingCoreRepresentation (Fin 7)) πX F.symm.toLinearMap
      (fun x v => by
        apply F.injective
        change F (E.chosenAction (inclusion hXY x) (F.symm v)) =
          F (F.symm (BinaryPermutation.coreRepresentation (Fin 7) (π (inclusion hXY x)).val v))
        rw [hF,F.apply_symm_apply,F.apply_symm_apply]) ⊤ ⊤
    rw [Submodule.map_top,LinearEquiv.range,hi] at hm
    change (F.symm.toLinearMap.comp j0).range = _
    rw [LinearMap.range_comp,hr0]
    exact hm.symm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X Y W : Subgroup G}

/-- The remaining deleted-seven row contradicts the original TI-pair quadratic action. -/
theorem HStarGeneratingComponent.not_proper_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) : False := by
  let := E.actionCentralizer_normal
  obtain ⟨⟨a⟩,_⟩ := C.proper_seven_full_natural_at h D structural modules hnone hTI hH hXY hY E
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY.le hY
  have hr := C.eq_residual_of_normalized hTX
  obtain ⟨eX⟩ := C.five_of_overcomponent_at h D structural modules hTI hH hXY.le hY
  obtain ⟨q,hq,hkq,j,hj,he,hmoved⟩ := seven_five_embedding hXY.le hTX hY structural E a eX
  let e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hkq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have heq (x : X) : e (QuotientGroup.mk' (pCore 2 X) x) = q x := rfl
  let eK : pResidual 2 H ≃* X :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hr.symm)
  let eR := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
  have hm := chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH (fun _ => ⟨eR⟩))
  let Q := H.pCoreIn 2
  let N := X ⊔ Q
  have hKH : X ≤ H := C.component.1
  have hHX : H ≤ normalizer (X : Set G) := by rw [←C.generates]; exact sup_le X.le_normalizer hTX
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hNH : N ≤ H := sup_le hKH (pCoreIn_le 2 H)
  have hVN : V ≤ N := by
    simpa only [←hr] using chosen_hstar_le_residual_join_core_at h D structural hH eR
  have hWQ := overcomponent_chosen_le_hstar_core C structural hH hXY.le hY E
  have hWJ : W ≤ N := hWQ.trans le_sup_right
  have hc : Q.subgroupOf X = pCore 2 X := by
    change (H.pCoreIn 2).subgroupOf X = pCore 2 X
    rw [hr]
    exact residual_core_intersection
  obtain ⟨f,hf,hkf,hfk⟩ := core_join_projection X Q (hKH.trans hHQ) hc e
  have hfk' (x : X) : f (inclusion le_sup_left x) = q x := (hfk x).trans (heq x)
  let J := Y ⊔ (T : Subgroup G)
  have hHJ : H ≤ J := by rw [←C.generates]; exact sup_le_sup hXY.le le_rfl
  have hNJ : N ≤ J := hNH.trans hHJ
  let hT := ((structural Y hY).2.2 W E).1
  let τ := (joinAction E hT).comp (inclusion hNJ)
  let K := X.subgroupOf N
  let R := Q.subgroupOf N
  let d : K ≃* X := subgroupOfEquivOfLe le_sup_left
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hNH.trans hHX)
  let : R.Normal := normal_subgroupOf_of_le_normalizer (hNH.trans hHQ)
  have hR : IsPGroup 2 R := (isPGroup_pCoreIn 2 H).comap_subtype
  have hgen : K ⊔ R = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ←MonoidHom.range_eq_map,range_subtype]
  have hfK : Function.Surjective (f.comp K.subtype) := by
    intro b
    obtain ⟨x,rfl⟩ := hq b
    exact ⟨d.symm x,hfk' x⟩
  have ha (x : X) (v : E.space) :
      τ (inclusion le_sup_left x) v = E.chosenAction (inclusion hXY.le x) v := by
    change joinAction E hT (inclusion le_sup_left (inclusion hXY.le x)) v = _
    exact LinearMap.congr_fun (joinAction_component E hT
      ((subgroupOfEquivOfLe (show Y ≤ J from le_sup_left)).symm (inclusion hXY.le x))) v
  have heK (k : K) (v : BinaryPermutation.core (Fin 5)) :
      j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (f k) v) = τ k (j v) := by
    change j (BinaryPermutation.alternatingCoreRepresentation (Fin 5)
      (f (inclusion le_sup_left (d k))) v) = τ (inclusion le_sup_left (d k)) (j v)
    rw [hfk',ha]
    exact he (d k) v
  have hrange : j.range = subspaceCommutator τ ⊤ K := by
    rw [hmoved]
    have heρ : E.chosenAction.comp (inclusion hXY.le) = τ.comp (inclusion (show X ≤ N from le_sup_left)) := by
      apply MonoidHom.ext
      intro x
      apply LinearMap.ext
      intro v
      exact (ha x v).symm
    rw [heρ,subspaceCommutator_comp_map]
    congr 1
    ext n
    constructor
    · rintro ⟨x,_,rfl⟩
      exact x.property
    · intro hn
      exact ⟨⟨n,hn⟩,mem_top _,rfl⟩
  have hall := BinaryPermutation.five_moved_embedding_extends τ K R hR hgen f hfK
    (hkf.ge) j hj heK hrange
  have hNW : N ≤ normalizer (W : Set G) := hNJ.trans (sup_le E.normalizes hT)
  let sec : BinaryConjugationSection N W ⊥ τ := {
    section_le := hWJ
    kernel_le := bot_le
    normalized := hNW
    coordinates := E.spaceEquiv.symm.toMonoidHom
    onto := E.spaceEquiv.symm.surjective
    kernel_eq := by
      rw [E.spaceEquiv.symm.toMonoidHom.ker_eq_bot E.spaceEquiv.symm.injective,bot_subgroupOf]
    equivariant := by
      intro n w
      apply Multiplicative.ofAdd.injective
      apply E.spaceEquiv.injective
      change E.spaceEquiv (E.spaceEquiv.symm _) =
        E.spaceEquiv (Multiplicative.ofAdd (τ n (E.spaceEquiv.symm w).toAdd))
      rw [E.spaceEquiv.apply_symm_apply]
      apply Subtype.ext
      have hh := chosen_join_conjugation E hT (inclusion hNJ n) (E.spaceEquiv.symm w).toAdd
      change (E.spaceEquiv (Multiplicative.ofAdd (τ n (E.spaceEquiv.symm w).toAdd)) : G) = _ at hh
      change (E.spaceEquiv (Multiplicative.ofAdd (τ n (E.spaceEquiv.symm w).toAdd)) : G) =
        (n : G) * (E.spaceEquiv (E.spaceEquiv.symm w) : G) * (n : G)⁻¹ at hh
      rw [E.spaceEquiv.apply_symm_apply] at hh
      exact hh.symm }
  apply chosen_hstar_no_five_embedded_at h D structural hTI hH N hNH hVN f hf hkf.le
    (fun hv => hm (fun v hv' => hkf.le (hv (show (⟨v,hVN hv'⟩ : N) ∈ V.subgroupOf N from hv'))))
    τ W hWQ sec j hj hall

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
