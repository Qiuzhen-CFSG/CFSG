module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientNonFFLayer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOriginal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianCover
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.GroupTheory.NormalModuleCore
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianCover

/-!
# An invariant Hermitian seed exhausts the original fixed-free module

The actual seed is reduced because its faithful component model detects the
same two-core as the original module. Chapter K makes its literal quotient
action non-FF when the Hermitian half-degree exceeds one. Its inclusion into
the original module is an intertwiner for the same quotient actor. The original
cubic and two-section budget therefore put every component displacement in
the seed. Hermitian first-cohomology vanishing then splits off the original
fixed subgroup, which is trivial by hypothesis.

Source: Aschbacher--Smith 5.1.3, printed pp.630--631, using B.6.9 and I.1.6(3).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W U : Subgroup G} {n s : ℕ} [NeZero s]

attribute [local instance] SL2.BinarySmall.spaceBinaryModule

private theorem Input.hermitian_seed_input
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s)) :
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
      (hm.centralizer_eq_core (OrthogonalFourMinus.RankOne.hermitian_injective s))
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

/-- An actual Sylow-invariant Hermitian seed of half-degree greater than
one is the whole original module when its component fixed subgroup is trivial.
No quotient triviality, section non-FF, or cohomology premise is supplied. -/
theorem Input.eq_hermitian_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hc : W ⊓ centralizer (L : Set G) = ⊥) : W = U := by
  have hU := h.hermitian_seed_input hUW hTU hm
  let J := L ⊔ (T : Subgroup G)
  let V₀ := W.subgroupOf J
  let U₀ := U.subgroupOf J
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let := hU.reduced_internal.normal
  let := hU.reduced_internal.elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq := QuotientGroup.mk'_surjective (pCore 2 J)
  have hk : q.ker = centralizer (V₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
  have hkU : q.ker = centralizer (U₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans hU.reduced_centralizer_eq_twoCore.symm
  let ρ := NormalElementaryQuotient.representation V₀ q hq hk
  let σ := NormalElementaryQuotient.representation U₀ q hq hkU
  let K := (L.subgroupOf J).map q
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
  have hnonσ : ¬ IsFFModule σ := by
    obtain ⟨hsource,⟨M⟩⟩ := hU.hermitian_original_source hm
    rcases (hsource.orthogonal_case M).2 with hn | ⟨hs1,_⟩
    · exact hn.2.2.2
    · omega
  have hnon : ¬ IsFFModule i.range.toRepresentation := by
    intro hh
    apply hnonσ
    apply hh.map_equivariant i.range.toRepresentation σ (MonoidHom.id _) Function.injective_id E.symm
    intro a v
    apply E.injective
    change E (E.symm (i.range.toRepresentation a v)) = E (σ a (E.symm v))
    rw [he,E.apply_symm_apply,E.apply_symm_apply]
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
  have hmoved := (h.moved_le_nonFF_section i.range hK hnon).2
  have hdisp (l : L) (w : W) :
      (l : G) * (w : G) * (l : G)⁻¹ * (w : G)⁻¹ ∈ U := by
    let l₀ : J := ⟨l,(show L ≤ J from le_sup_left) l.property⟩
    let w₀ : Additive V₀ := Additive.ofMul ⟨⟨w,h.reduced.1 w.property⟩,w.property⟩
    have hz : ρ (q l₀) w₀ - w₀ ∈ i.range.toSubmodule :=
      hmoved (Submodule.subset_span ⟨q l₀,mem_map_of_mem q l.property,w₀,by trivial,rfl⟩)
    obtain ⟨u,hu⟩ := hz
    have huJ := congrArg (fun z : Additive V₀ => (z.toMul : J)) hu
    rw [toMul_sub,div_eq_mul_inv] at huJ
    change (u.toMul : J) = ((ρ (q l₀) w₀).toMul : J) * (w₀.toMul : J)⁻¹ at huJ
    rw [NormalElementaryQuotient.representation_apply] at huJ
    have huG : ((u.toMul : J) : G) =
        (l : G) * (w : G) * (l : G)⁻¹ * (w : G)⁻¹ := congrArg J.subtype huJ
    rw [←huG]
    exact u.toMul.property
  obtain ⟨e,f,hf⟩ := hm
  let r := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hr : Function.Surjective r := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let := hermitian_H1 (s := s)
  have hsplit := sup_centralizer_eq_of_conjugation_H1 L W U hUW r hr
    (SL2.BinarySmall.hermitian s) f (by
      intro l v
      have hh := hf l (f.symm (Multiplicative.ofAdd v))
      simpa only [r,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        f.apply_symm_apply,toAdd_ofAdd] using hh) (by
      intro l hl
      have hlcore : l ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff l).mp
        apply e.injective
        exact hl.trans e.map_one.symm
      exact core_centralizes_original h (mem_map_of_mem L.subtype hlcore)) hdisp
  rw [hc,sup_bot_eq] at hsplit
  exact hsplit.symm

/-- The seed's original Hermitian quotient marking describes the whole
original module. -/
theorem Input.hermitian_model_of_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hUW : U ≤ W) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hc : W ⊓ centralizer (L : Set G) = ⊥) :
    IsConjugationModel L W (SL2.BinarySmall.hermitian s) := by
  exact (h.eq_hermitian_seed hUW hTU hm hs hc).symm ▸ hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
