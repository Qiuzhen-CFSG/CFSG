module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFour
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The normalizer and central line of the exceptional A₇ four-space

The faithful A₇ image is self-normalizing in GL₄(2). Since N_G(V) normalizes
L, its action on the original chosen space is already induced by L. This
gives the literal factorization N_G(V)=L C_G(V), retaining its ambient
multiplication and original inclusion of V.

A Sylow subgroup of L obtained from T∩L maps onto a Sylow subgroup of A₇.
The unique nonzero fixed vector in the faithful four-space therefore gives
the actual central line V∩Ω₁(Z(T))=⟨z⟩. Transitivity transfers the allowed
12.2.13 escape to C_G(z). The residual and component arguments needed to
exclude the four-space remain separate source obligations.

Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808.
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

private def spaceLinear : letI := S.chosen.elementary
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

private def normalizerAction : Representation (ZMod 2) (normalizer (V : Set G))
    S.chosen.space := by
  letI := S.chosen.elementary
  exact S.spaceLinear.symm.conjRingEquiv.toMonoidHom.comp
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizerAction_component (l : L) :
    S.normalizerAction ⟨l, S.chosen.normalizes l.property⟩ = S.chosen.chosenAction l := by
  letI := S.chosen.elementary
  apply LinearMap.ext
  intro v
  apply S.spaceLinear.injective
  change S.spaceLinear (S.spaceLinear.symm _) = _
  rw [S.spaceLinear.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [LinearEquiv.symm_symm]
  change (l : G) * (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ =
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l v)) : G)
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem normalizerAction_conjugation (n : normalizer (V : Set G))
    (v : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.normalizerAction n v)) : G) =
      (n : G) * (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G) * (n : G)⁻¹ := by
  letI := S.chosen.elementary
  have h := S.spaceLinear.apply_symm_apply
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom n (S.spaceLinear v))
  exact congrArg (fun w : Additive V => (w.toMul : G)) h

private theorem four_normalizer_action
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (n : normalizer (V : Set G)) :
    ∃ l : L, S.normalizerAction n = S.chosen.chosenAction l := by
  letI := S.chosen.actionCentralizer_normal
  let ρ := S.normalizerAction
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
      exact (S.normalizerAction_component ⟨l,hl⟩).symm
    · rintro ⟨a,rfl⟩
      obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
        ((centralizer (V : Set G)).subgroupOf L) (e.symm a)
      refine ⟨⟨l,S.chosen.normalizes l.property⟩,l.property,?_⟩
      apply Units.ext
      change S.normalizerAction _ = S.chosen.faithfulAction (e.symm a)
      rw [←hl,S.chosen.faithfulAction_mk,S.normalizerAction_component]
  have hLN : normalizer (L' : Set (normalizer (V : Set G))) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (S.normalizer_le_component structural x.property) l.val
  have hh := L'.le_normalizer_map ρ.asGroupHom
  rw [hLN,himg,BinaryAlternatingSevenControl.actionImage_self_normalizing σ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd] at hh
  have hn : ρ.asGroupHom n ∈ L'.map ρ.asGroupHom := by
    rw [himg]
    exact hh (mem_map_of_mem _ (mem_top n))
  obtain ⟨l,hl,he⟩ := hn
  refine ⟨⟨l,hl⟩,?_⟩
  exact (congrArg Units.val he).symm.trans (S.normalizerAction_component ⟨l,hl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the full normalizer is an L-element times an element
of the literal ambient centralizer of V. -/
theorem four_normalizer_factorization
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L, ∃ c ∈ centralizer (V : Set G), n = l * c := by
  intro n hn
  obtain ⟨l,hl⟩ := S.four_normalizer_action structural e hd ⟨n,hn⟩
  refine ⟨l,l.property,(l:G)⁻¹*n,?_,by group⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
  have hval : (S.chosen.spaceEquiv w : G) = v := congrArg Subtype.val hw
  have hh := LinearMap.congr_fun (hl.trans (S.normalizerAction_component l).symm) w.toAdd
  have he := congrArg (fun w : S.chosen.space =>
    (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) hh
  rw [S.normalizerAction_conjugation,S.normalizerAction_conjugation] at he
  have hh := congrArg (fun x : G => (l:G)⁻¹*x*(l:G)) he
  have hc : ((l:G)⁻¹*n) * (S.chosen.spaceEquiv w : G) * ((l:G)⁻¹*n)⁻¹ =
      (S.chosen.spaceEquiv w : G) := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, ofAdd_toAdd] using hh
  rw [hval] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem sylow_fixed_line_space
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ v : S.chosen.space, v ≠ 0 ∧
      (∀ t : T, S.normalizerAction ⟨t,((structural G T L S.hypothesis).2.2 V S.chosen).1 t.property⟩ v = v) ∧
      ∀ w : S.chosen.space,
        (∀ t : T, S.normalizerAction ⟨t,((structural G T L S.hypothesis).2.2 V S.chosen).1 t.property⟩ w = w) →
        w = 0 ∨ w = v := by
  letI := S.chosen.actionCentralizer_normal
  have hT : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    ((structural G T L S.hypothesis).2.2 V S.chosen).1
  let τ := S.normalizerAction.comp (inclusion hT)
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
      (hw : ∀ t : T, S.normalizerAction ⟨t,hT t.property⟩ w = w) : w ∈ fixedSpace σ R := by
    intro a
    obtain ⟨l,hl,he⟩ := a.property
    have hlT : (l.val.val : G) ∈ T := (hP.le (mem_map_of_mem L'.subtype hl)).1
    have hh := hw ⟨l.val.val,hlT⟩
    rw [S.normalizerAction_component ⟨l.val.val,l.property⟩] at hh
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
/-- The central line is the actual T-fixed subgroup of the original V. -/
theorem four_sylow_fixed_line
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∈ centralizer (T : Set G) ∧
      ∀ w ∈ V, w ∈ centralizer (T : Set G) → w = 1 ∨ w = z := by
  obtain ⟨v,hv,hfix,hunique⟩ := S.sylow_fixed_line_space structural e hd
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
    rw [S.normalizerAction_conjugation] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro w hw hwT
    obtain ⟨a,ha⟩ := S.chosen.spaceEquiv.surjective ⟨w,hw⟩
    have hval : (S.chosen.spaceEquiv a : G) = w := congrArg Subtype.val ha
    have hfixed : ∀ t : T, S.normalizerAction
        ⟨t,((structural G T L S.hypothesis).2.2 V S.chosen).1 t.property⟩ a.toAdd = a.toAdd := by
      intro t
      apply hinj
      dsimp only
      rw [S.normalizerAction_conjugation,ofAdd_toAdd,hval]
      exact mul_inv_eq_iff_eq_mul.mpr (hwT t t.property)
    rcases hunique a.toAdd hfixed with he | he
    · left
      exact hval.symm.trans ((congrArg (fun w : S.chosen.space =>
        (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) he).trans hzero)
    · right
      exact hval.symm.trans (congrArg (fun w : S.chosen.space =>
        (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) he)

/-- The source central involution and its escaping ambient centralizer. -/
theorem four_central_line
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∈ omegaCenterIn (T : Subgroup G) ∧
      V ⊓ omegaCenterIn (T : Subgroup G) = zpowers z ∧
      Nat.card (V ⊓ omegaCenterIn (T : Subgroup G) : Subgroup G) = 2 ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  letI := S.chosen.elementary
  obtain ⟨z,hz,hz1,hzT,hunique⟩ := S.four_sylow_fixed_line structural e hd
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
