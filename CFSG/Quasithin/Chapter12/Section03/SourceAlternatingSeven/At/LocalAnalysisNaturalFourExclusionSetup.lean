module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSetup
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer

/-!
# LocalAnalysisNaturalFourExclusionSetup at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionSetup`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

public noncomputable section

set_option linter.style.haveILetI false

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private def spaceLinear_at : letI := S.chosen.elementary
    S.chosen.space ≃ₗ[ZMod 2] Additive V := by
  letI := S.chosen.elementary
  let f : S.chosen.space ≃+ Additive V :=
    { toFun v := Additive.ofMul (S.chosen.spaceEquiv (Multiplicative.ofAdd v))
      invFun v := (S.chosen.spaceEquiv.symm v.toMul).toAdd
      left_inv v := congrArg Multiplicative.toAdd
        (S.chosen.spaceEquiv.symm_apply_apply (Multiplicative.ofAdd v))
      right_inv v := congrArg Additive.ofMul (S.chosen.spaceEquiv.apply_symm_apply v.toMul)
      map_add' v w := congrArg Additive.ofMul (S.chosen.spaceEquiv.map_mul
        (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  exact f.toLinearEquiv (ZMod.map_smul f)

private def normalizerAction_at : Representation (ZMod 2) (normalizer (V : Set G))
    S.chosen.space := by
  letI := S.chosen.elementary
  exact S.spaceLinear_at.symm.conjRingEquiv.toMonoidHom.comp
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom)

set_option backward.isDefEq.respectTransparency false in

private theorem normalizerAction_component_at (l : L) :
    S.normalizerAction_at ⟨l, S.chosen.normalizes l.property⟩ = S.chosen.chosenAction l := by
  letI := S.chosen.elementary
  apply LinearMap.ext
  intro v
  apply S.spaceLinear_at.injective
  change S.spaceLinear_at (S.spaceLinear_at.symm _) = _
  rw [S.spaceLinear_at.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [LinearEquiv.symm_symm]
  change (l : G) * (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ =
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l v)) : G)
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem normalizerAction_conjugation_at (n : normalizer (V : Set G))
    (v : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.normalizerAction_at n v)) : G) =
      (n : G) * (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G) * (n : G)⁻¹ := by
  letI := S.chosen.elementary
  have h := S.spaceLinear_at.apply_symm_apply
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom n (S.spaceLinear_at v))
  exact congrArg (fun w : Additive V => (w.toMul : G)) h

private theorem four_normalizer_action_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (n : normalizer (V : Set G)) :
    ∃ l : L, S.normalizerAction_at n = S.chosen.chosenAction l := by
  letI := S.chosen.actionCentralizer_normal
  let ρ := S.normalizerAction_at
  let σ := S.chosen.faithfulAction.comp e.symm.toMonoidHom
  let L' := L.subgroupOf (normalizer (V : Set G))
  have himg : L'.map ρ.asGroupHom = actionImage σ := by
    ext a
    constructor
    · rintro ⟨l,hl,rfl⟩
      refine ⟨e (QuotientGroup.mk' _ ⟨l,hl⟩), ?_⟩
      apply Units.ext
      change S.chosen.faithfulAction (e.symm (e _)) = _
      rw [e.symm_apply_apply,S.chosen.faithfulAction_mk]
      exact (S.normalizerAction_component_at ⟨l,hl⟩).symm
    · rintro ⟨a,rfl⟩
      obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
        ((centralizer (V : Set G)).subgroupOf L) (e.symm a)
      refine ⟨⟨l,S.chosen.normalizes l.property⟩,l.property,?_⟩
      apply Units.ext
      change S.normalizerAction_at _ = S.chosen.faithfulAction (e.symm a)
      rw [←hl,S.chosen.faithfulAction_mk,S.normalizerAction_component_at]
  have hLN : normalizer (L' : Set (normalizer (V : Set G))) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (S.normalizer_le_component_at structural x.property) l.val
  have hh := L'.le_normalizer_map ρ.asGroupHom
  rw [hLN,himg,BinaryAlternatingSevenControl.actionImage_self_normalizing σ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd] at hh
  have hn : ρ.asGroupHom n ∈ L'.map ρ.asGroupHom := by
    rw [himg]
    exact hh (mem_map_of_mem _ (mem_top n))
  obtain ⟨l,hl,he⟩ := hn
  refine ⟨⟨l,hl⟩,?_⟩
  exact (congrArg Units.val he).symm.trans (S.normalizerAction_component_at ⟨l,hl⟩)

set_option backward.isDefEq.respectTransparency false in

theorem four_normalizer_factorization_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L, ∃ c ∈ centralizer (V : Set G), n = l * c := by
  intro n hn
  obtain ⟨l,hl⟩ := S.four_normalizer_action_at structural e hd ⟨n,hn⟩
  refine ⟨l,l.property,(l:G)⁻¹*n,?_,by group⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
  have hval : (S.chosen.spaceEquiv w : G) = v := congrArg Subtype.val hw
  have hh := LinearMap.congr_fun (hl.trans (S.normalizerAction_component_at l).symm) w.toAdd
  have he := congrArg (fun w : S.chosen.space =>
    (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) hh
  rw [S.normalizerAction_conjugation_at,S.normalizerAction_conjugation_at] at he
  have hh := congrArg (fun x : G => (l:G)⁻¹*x*(l:G)) he
  have hc : ((l:G)⁻¹*n) * (S.chosen.spaceEquiv w : G) * ((l:G)⁻¹*n)⁻¹ =
      (S.chosen.spaceEquiv w : G) := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, ofAdd_toAdd] using hh
  rw [hval] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem sylow_fixed_line_space_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ v : S.chosen.space, v ≠ 0 ∧
      (∀ t : T, S.normalizerAction_at ⟨t,((structural L S.hypothesis).2.2 V S.chosen).1 t.property⟩ v = v) ∧
      ∀ w : S.chosen.space,
        (∀ t : T, S.normalizerAction_at ⟨t,((structural L S.hypothesis).2.2 V S.chosen).1 t.property⟩ w = w) →
        w = 0 ∨ w = v := by
  letI := S.chosen.actionCentralizer_normal
  have hT : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    ((structural L S.hypothesis).2.2 V S.chosen).1
  let τ := S.normalizerAction_at.comp (inclusion hT)
  letI : Nontrivial S.chosen.space := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) S.chosen.space)
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector τ T.isPGroup'
  let H := L ⊔ (T : Subgroup G)
  let L' := L.subgroupOf H
  letI : L'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype le_sup_right).exists_sylow_map_eq_inf_of_normal L'
  let f : L' →* alternatingGroup (Fin 7) :=
    (e.toMonoidHom.comp (QuotientGroup.mk' _)).comp
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).toMonoidHom
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
  let R := P.mapSurjective hf
  let σ := S.chosen.faithfulAction.comp e.symm.toMonoidHom
  have hfixed (w : S.chosen.space)
      (hw : ∀ t : T, S.normalizerAction_at ⟨t,hT t.property⟩ w = w) : w ∈ fixedSpace σ R := by
    intro a
    obtain ⟨l,hl,he⟩ := a.property
    have hlT : (l.val.val : G) ∈ T := (hP.le (mem_map_of_mem L'.subtype hl)).1
    have hh := hw ⟨l.val.val,hlT⟩
    rw [S.normalizerAction_component_at ⟨l.val.val,l.property⟩] at hh
    change S.chosen.faithfulAction (e.symm a.val) w = w
    rw [←he]
    change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ ⟨l.val.val,l.property⟩))) w = w
    rw [e.symm_apply_apply,S.chosen.faithfulAction_mk]
    exact hh
  obtain ⟨u,hu,huR,hunique⟩ := BinaryAlternatingSevenControl.sylow_fixed_line σ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd R
  have hvu : v = u := (hunique v (hfixed v hfix)).resolve_left hv
  refine ⟨v,hv,hfix,?_⟩
  intro w hw
  simpa only [←hvu] using hunique w (hfixed w hw)

set_option backward.isDefEq.respectTransparency false in

theorem four_sylow_fixed_line_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∈ centralizer (T : Set G) ∧
      ∀ w ∈ V, w ∈ centralizer (T : Set G) → w = 1 ∨ w = z := by
  obtain ⟨v,hv,hfix,hunique⟩ := S.sylow_fixed_line_space_at structural e hd
  let z : G := S.chosen.spaceEquiv (Multiplicative.ofAdd v)
  have hinj : Function.Injective (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) :=
    Subtype.val_injective.comp (S.chosen.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  have hzero : (S.chosen.spaceEquiv (Multiplicative.ofAdd (0 : S.chosen.space)) : G) = 1 :=
    congrArg Subtype.val S.chosen.spaceEquiv.map_one
  refine ⟨z,(S.chosen.spaceEquiv (Multiplicative.ofAdd v)).property,?_,?_,?_⟩
  · intro hz
    exact hv (hinj (hz.trans hzero.symm))
  · intro t ht
    have hh := congrArg (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) (hfix ⟨t,ht⟩)
    rw [S.normalizerAction_conjugation_at] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro w hw hwT
    obtain ⟨a,ha⟩ := S.chosen.spaceEquiv.surjective ⟨w,hw⟩
    have hval : (S.chosen.spaceEquiv a : G) = w := congrArg Subtype.val ha
    have hfixed : ∀ t : T, S.normalizerAction_at
        ⟨t,((structural L S.hypothesis).2.2 V S.chosen).1 t.property⟩ a.toAdd = a.toAdd := by
      intro t
      apply hinj
      dsimp only
      rw [S.normalizerAction_conjugation_at,ofAdd_toAdd,hval]
      exact mul_inv_eq_iff_eq_mul.mpr (hwT t t.property)
    rcases hunique a.toAdd hfixed with he | he
    · left
      exact hval.symm.trans ((congrArg (fun w : S.chosen.space =>
        (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) he).trans hzero)
    · right
      exact hval.symm.trans (congrArg (fun w : S.chosen.space =>
        (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) he)

theorem four_central_line_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∈ omegaCenterIn (T : Subgroup G) ∧
      V ⊓ omegaCenterIn (T : Subgroup G) = zpowers z ∧
      Nat.card (V ⊓ omegaCenterIn (T : Subgroup G) : Subgroup G) = 2 ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  letI := S.chosen.elementary
  obtain ⟨z,hz,hz1,hzT,hunique⟩ := S.four_sylow_fixed_line_at structural e hd
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz
  have hzO : z ∈ omegaCenterIn (T : Subgroup G) :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow hz,hzT,hz2⟩
  have he : V ⊓ omegaCenterIn (T : Subgroup G) = zpowers z := by
    apply le_antisymm
    · intro x hx
      rcases hunique x hx.1 ((mem_omegaCenterIn_iff _ _).mp hx.2).2.1 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · exact zpowers_le.mpr ⟨hz,hzO⟩
  refine ⟨z,hz,hz1,hzO,he,?_,S.four_all_pointCentralizers_escape escape e hd hz hz1⟩
  rw [he,Nat.card_zpowers]
  exact orderOf_eq_prime hz2 hz1

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

