module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSectionBudget
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledThompson
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.GroupTheory.NormalModuleCore
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientNaturalSeedRank
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientRank
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families

/-!
# A proper invariant natural seed forces original Thompson centralization

The actual seed and its proper quotient are noncentral for the component.
The original section budget makes each consume one actor rank. Every nonzero
elementary actor moves at least n binary dimensions on the natural seed,
including actors inducing outer field automorphisms. A near-maximum actor
would therefore have both full codimension twice its rank and codimension
at most its rank plus one, impossible for n>1. Thus J₁(T) centralizes the
whole original moved layer.

Source: Aschbacher--Smith 6.1.4, printed pp.664--665, with B.6.9 and B.2.4.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W U : Subgroup G} {n : ℕ}
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem Input.natural_seed_input
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : IsConjugationModel L U (specialLinearNatural (k := F) 2)) :
    Input KnownSimple.IsKnownSimple T L U n := by
  let J := L ⊔ (T : Subgroup G)
  let V₀ := W.subgroupOf J
  let U₀ := U.subgroupOf J
  have hUJ : U ≤ J := hUW.trans h.reduced.1
  have hJU : J ≤ normalizer (U : Set G) := sup_le hm.normalizes hTU
  let := h.reduced_internal.normal
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer hJU
  have hcoreW : J.pCoreIn 2 ≤ centralizer (W : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ w hw
    have hxC : x ∈ centralizer (V₀ : Set J) := h.reduced_centralizer_eq_twoCore.ge hx
    exact congrArg J.subtype (hxC ⟨w,h.reduced.1 hw⟩ hw)
  have hC : J ⊓ centralizer (U : Set G) = J.pCoreIn 2 :=
    ambient_centralizer_eq_core_of_normal_supplement L U T h.sylow_normalizes
      hUJ hJU T.isPGroup'
      (hm.centralizer_eq_core (specialLinearNatural_injective 2))
      (hcoreW.trans (centralizer_le hUW))
  have hC₀ : centralizer (U₀ : Set J) = pCore 2 J := by
    apply map_injective J.subtype_injective
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hUJ]
    exact hC
  have hred : U ∈ reducedFamily J := by
    let := h.reduced.2.1
    refine ⟨hUJ,IsElementaryAbelian.of_le hUW,⟨inferInstance,?_⟩⟩
    let e := QuotientGroup.quotientMulEquivOfEq hC₀
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso 2 e,Subgroup.map_bot]
    exact pCore_quotient_pCore_eq_bot 2
  have hnon : ⁅U,L⁆ ≠ ⊥ := by
    intro hz
    have hLC : L ≤ centralizer (U : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hz)
    apply h.noncentral
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro l hl
    exact hcoreW (hC.le ⟨(show L ≤ J from le_sup_left) hl,hLC hl⟩)
  exact { h with reduced := hred, noncentral := hnon }

private theorem natural_fixedCodim_lower
    {D X : Type*} [Group D]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (K : Subgroup D) [K.Normal]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hC : centralizer (K : Set D) = ⊥)
    (ρ : Representation (ZMod 2) D X)
    (c : X ≃ₗ[ZMod 2] (Fin 2 → F))
    (hc : ∀ (l : K) x, c (ρ l x) = specialLinearNatural 2 (e l) (c x))
    (hF : Nat.card F = 2 ^ n) (A : Subgroup D) (hA : IsElementaryTwo A) :
    n ≤ fixedCodim ρ A := by
  let a : D →* MulAut K := MulAut.conjNormal
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro x hx
    apply hC.le
    intro l hl
    have hh := congrArg (fun z : MulAut K => (z ⟨l,hl⟩ : D)) hx
    change x * l * x⁻¹ = l at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨x,hx,hx1⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hA.1)
  have hxne : x ≠ 1 := by simpa only [mem_bot] using hx1
  let := hA.2
  have hx2 : x*x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
  let b : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := (MulAut.congr e) (a x)
  have hb2 : b*b = 1 := by
    change (MulAut.congr e) (a x) * (MulAut.congr e) (a x) = 1
    rw [←map_mul,←map_mul,hx2,map_one,map_one]
  have hb : b ≠ 1 := by
    intro hh
    apply hxne
    apply ha
    apply (MulAut.congr e).injective
    simpa only [map_one] using hh
  let σ := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let c₁ := c.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → F)).symm
  have hbound := AlternatingFive.AmplifiedNatural.automorphism_involution_bound F hF
    σ c₁ (by
      intro g v
      funext j
      change c (ρ (e.symm g : D) v) = specialLinearNatural 2 g (c v)
      simpa only [e.apply_symm_apply] using hc (e.symm g) v)
    (ρ x) (ρ.apply_bijective x).injective b hb2 hb (by
      intro g v
      change ρ x (ρ (e.symm g : D) v) = ρ (e.symm (b g) : D) (ρ x v)
      have he : (e.symm (b g) : D) = x * (e.symm g : D) * x⁻¹ := by
        change (e.symm (e (MulAut.conjNormal x (e.symm g))) : D) = _
        rw [e.symm_apply_apply]
        rfl
      rw [he,←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul]
      congr 1
      group)
  have hb' : n ≤ operatorFixedCodim (ρ x) := by
    simpa only [Fintype.card_fin,one_mul] using hbound
  exact hb'.trans (operatorFixedCodim_le_fixedCodim ρ A hx)

private theorem Input.proper_natural_seed_thompson_centralizes
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : IsConjugationModel L U (specialLinearNatural (k := F) 2))
    (hF : Nat.card F = 2 ^ n) (hfull : ⁅W,L⁆ = W) (hproper : U ≠ W) :
    ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (W : Set G) := by
  have hU := h.natural_seed_input hUW hTU hm
  let J := L ⊔ (T : Subgroup G)
  let V₀ := W.subgroupOf J
  let U₀ := U.subgroupOf J
  let B := L.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let := hU.reduced_internal.normal
  let := hU.reduced_internal.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq := QuotientGroup.mk'_surjective (pCore 2 J)
  have hk : q.ker = centralizer (V₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
  have hkU : q.ker = centralizer (U₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans hU.reduced_centralizer_eq_twoCore.symm
  let ρ := NormalElementaryQuotient.representation V₀ q hq hk
  let σ := NormalElementaryQuotient.representation U₀ q hq hkU
  let K := B.map q
  let : K.Normal := (inferInstance : B.Normal).map q hq
  let j : U₀ →* V₀ := inclusion (show U₀ ≤ V₀ from fun _ hx => hUW hx)
  let i : σ.IntertwiningMap ρ := {
    toLinearMap := j.toAdditive.toZModLinearMap 2
    isIntertwining' := by
      intro a
      obtain ⟨g,rfl⟩ := hq a
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((σ (q g) u).toMul : J) = ((ρ (q g) (j.toAdditive.toZModLinearMap 2 u)).toMul : J)
      rw [NormalElementaryQuotient.representation_apply,
        NormalElementaryQuotient.representation_apply]
      rfl }
  have hi : Function.Injective i.toLinearMap := by
    intro u v he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Additive V₀ => (z.toMul : J)) he
  let E := LinearEquiv.ofInjective i.toLinearMap hi
  have he (a : J ⧸ pCore 2 J) (u : Additive U₀) :
      E (σ a u) = i.range.toRepresentation a (E u) :=
    Subtype.ext (LinearMap.congr_fun (i.isIntertwining' a) u)
  have hK : ¬ K ≤ i.range.toRepresentation.ker := by
    intro hh
    apply hU.noncentral
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro u hu l hl
    let l₀ : J := ⟨l,(show L ≤ J from le_sup_left) hl⟩
    let u₀ : Additive U₀ := Additive.ofMul ⟨⟨u,hU.reduced.1 hu⟩,hu⟩
    have hz : i.range.toRepresentation (q l₀) (E u₀) = E u₀ :=
      DFunLike.congr_fun (hh (mem_map_of_mem q hl)) (E u₀)
    have hz' : σ (q l₀) u₀ = u₀ := E.injective ((he _ _).trans hz)
    have hzJ := congrArg (fun z : Additive U₀ => (z.toMul : J)) hz'
    rw [NormalElementaryQuotient.representation_apply] at hzJ
    exact mul_inv_eq_iff_eq_mul.mp (congrArg J.subtype hzJ)
  have hquot : ¬ K ≤ i.range.quotientRepresentation.ker := by
    intro hh
    apply hproper
    apply le_antisymm hUW
    rw [←hfull,commutator_comm]
    apply commutator_le.mpr
    intro l hl w hw
    let l₀ : J := ⟨l,(show L ≤ J from le_sup_left) hl⟩
    let w₀ : Additive V₀ := Additive.ofMul ⟨⟨w,h.reduced.1 hw⟩,hw⟩
    have hz := DFunLike.congr_fun (hh (mem_map_of_mem q (show l₀ ∈ B from hl)))
      (i.range.toSubmodule.mkQ w₀)
    change i.range.quotientRepresentation (q l₀) (i.range.toSubmodule.mkQ w₀) =
      i.range.toSubmodule.mkQ w₀ at hz
    rw [i.range.quotientRepresentation_mk] at hz
    have hv : ρ (q l₀) w₀ - w₀ ∈ i.range.toSubmodule :=
      (Submodule.Quotient.eq i.range.toSubmodule).mp hz
    obtain ⟨u,hu⟩ := hv
    have huJ := congrArg (fun z : Additive V₀ => (z.toMul : J)) hu
    rw [toMul_sub,div_eq_mul_inv] at huJ
    change (u.toMul : J) = ((ρ (q l₀) w₀).toMul : J) * (w₀.toMul : J)⁻¹ at huJ
    rw [NormalElementaryQuotient.representation_apply] at huJ
    have huG : ((u.toMul : J) : G) = ⁅l,w⁆ := congrArg J.subtype huJ
    rw [←huG]
    exact u.toMul.property
  obtain ⟨e0,f0,hf0⟩ := hm
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eB : K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (coreQuotientEquivImage 2 B).symm.trans
      ((QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)).trans e0)
  have hsup : B ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K ((S : Subgroup J).map q) (S.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eB.map_eq_one_iff.mp
    exact (Theory.PSL2.sl2_center_eq_bot F).le (MulEquivClass.apply_mem_center eB hx)
  have hC : centralizer (K : Set (J ⧸ pCore 2 J)) = ⊥ := by
    have hp := centralizer_isPGroup_of_centerless_quotient K hz htwo
    have hh : centralizer (K : Set (J ⧸ pCore 2 J)) ≤ pCore 2 (J ⧸ pCore 2 J) :=
      le_sSup ⟨inferInstance,hp⟩
    exact bot_unique (hh.trans_eq (pCore_quotient_pCore_eq_bot (G:=J) 2))
  let uU : U₀ ≃* U := subgroupOfEquivOfLe hU.reduced.1
  let f := uU.trans f0
  let c : Additive U₀ ≃ₗ[ZMod 2] (Fin 2 → F) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  have hc : ∀ (l : K) x, c (σ l x) = specialLinearNatural 2 (eB l) (c x) := by
    intro l x
    obtain ⟨b,hb⟩ := q.subgroupMap_surjective B l
    let l0 : L := eb b
    have heB : eB (q.subgroupMap B b) = e0 (QuotientGroup.mk' (pCore 2 L) l0) := by
      change e0 (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb _
        ((coreQuotientEquivImage 2 B).symm (q.subgroupMap B b))) = _
      have heq : coreQuotientEquivImage 2 B (QuotientGroup.mk' (pCore 2 B) b) =
          q.subgroupMap B b := by
        apply Subtype.ext
        exact coreQuotientEquivImage_apply_mk 2 B b
      rw [←heq,MulEquiv.symm_apply_apply]
      rfl
    subst l
    rw [heB]
    let v : U := uU x.toMul
    have hact := hf0 l0 v
    have hcoords := congrArg f0
      (show f0.symm (Multiplicative.ofAdd
        (specialLinearNatural 2
          (e0 (QuotientGroup.mk' (pCore 2 L) l0)) (f0 v).toAdd)) =
        U.normalizerMonoidHom ⟨l0,(le_sup_left.trans (reduced_normalizes hU.reduced)) l0.property⟩ v from
          Subtype.ext hact)
    rw [f0.apply_symm_apply] at hcoords
    change c (NormalElementaryQuotient.representation U₀ q hq hkU (q b.val) x) = _
    apply Eq.trans ?_ (congrArg Multiplicative.toAdd hcoords.symm)
    apply congrArg (fun w : U => (f0 w).toAdd)
    apply Subtype.ext
    change (((NormalElementaryQuotient.representation U₀ q hq hkU (q b.val) x).toMul : J) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  have hVS : V₀ ≤ (S : Subgroup J) := h.reduced_internal.le_pCore.trans
    (pCore_isPGroup.le_sylow_of_normal S)
  have hTh : ChapterB.thompsonJ (S : Subgroup J) 1 ≤ centralizer (V₀ : Set J) := by
    apply sSup_le
    intro A hA
    by_contra hAC
    have hne : A.map q ≠ ⊥ := by
      intro hzero
      exact hAC (hk ▸ (map_eq_bot_iff A).mp hzero)
    let := hA.2.1
    have hEA : IsElementaryTwo (A.map q) := ⟨hne,IsElementaryAbelian.map q⟩
    have hnear := ChapterB.near_maximum_action_codimension (S : Subgroup J) V₀ hVS q hq hk hA hne
    change fixedCodim ρ (A.map q) ≤ rank (A.map q) + 1 at hnear
    have hpos := hEA.rank_pos
    have hbudget : fixedCodim ρ (A.map q) ≤ 2 * rank (A.map q) := by omega
    obtain ⟨_,_,hseed,_,hwhole,_,_,_,_⟩ :=
      h.original_section_offender_budget i.range hK hquot (A.map q) hEA hbudget
    change fixedCodim ρ (A.map q) = 2 * rank (A.map q) at hwhole
    have hlow := natural_fixedCodim_lower K eB hC σ c hc hF (A.map q) hEA
    have hecod := fixedCodim_map_equivariant σ i.range.toRepresentation (MonoidHom.id _) E he (A.map q)
    rw [Subgroup.map_id] at hecod
    have hn := h.exponent
    omega
  have hSm : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hVm : V₀.map J.subtype = W := map_subgroupOf_eq_of_le h.reduced.1
  rw [←hSm,ChapterB.thompsonJ_map_injective J.subtype J.subtype_injective]
  rintro x ⟨x,hx,rfl⟩ w hw
  obtain ⟨v,hv,rfl⟩ := hVm.symm ▸ hw
  exact congrArg J.subtype (hTh hx v hv)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V B : Subgroup G} {n : ℕ}

/-- A proper invariant natural seed forces J₁(T) to centralize the entire
literal original moved layer. All quotient and numerical conditions are derived. -/
theorem original_proper_natural_seed_thompson_centralizes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hB : B ≤ layer L V) (hnatural : IsNaturalModule L B n)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hproper : B ≠ layer L V) :
    ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (layer L V : Set G) := by
  obtain ⟨F,_,_,_,hF,hm⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfull : ⁅layer L V,L⁆ = layer L V := by
    let := h.V_mem.2.1
    exact commutator_isPPerfect_idempotent L V
      (Chapter1.Section02.Adequate.mem_L_isPPerfect h.local_mem.1.prop)
      (IsElementaryAbelian.isPGroup 2 V)
      (le_sup_left.trans (reduced_normalizes h.V_mem))
  exact (h.rankOneInput hout).commutator_input.proper_natural_seed_thompson_centralizes
    hB hTB hm hF hfull hproper

/-- Every Sylow-invariant natural seed is the entire original moved layer.
The rank contradiction uses the same layer and the original outside hypothesis. -/
theorem original_natural_seed_eq_layer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hB : B ≤ layer L V) (hnatural : IsNaturalModule L B n)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) : B = layer L V := by
  by_contra hn
  have hJ := original_proper_natural_seed_thompson_centralizes h hout hB hnatural hTB hn
  have hr := original_layer_rank_one_of_thompson_centralizes h hout hJ
  have hgt := original_natural_seed_one_lt_globalR h hB hnatural hTB
  rw [hr] at hgt
  exact (lt_irrefl _) hgt

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
