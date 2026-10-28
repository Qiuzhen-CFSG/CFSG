module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleThompsonNormalizer
public import Theory.GroupTheory.CComponent.Radical
public import Theory.GroupTheory.SolvableRadical.Transport
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonControl
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
/-!
# A normal C-component in the Sylow branch is a chi-zero block

C.1.29 gives an ordered product of actual chi-zero blocks outside the
characteristic-normalizer control subgroup. Every factor lies in the normal
component, since the quotient by that component is a two-group. If all
factors were proper, component minimality would put them in the solvable
radical. The ordered product would then make the marked proper intersection
surject onto the component modulo that radical. Its image remains proper:
modulo the two-core the radical is central, and perfectness removes central
supplements. Thus one selected block is the original component itself.

The final theorem restricts the original C.2.7 input to KR and supplies all
hypotheses from the actual Sylow assertion. No block witness is an input.
Source: Aschbacher–Smith C.1.29 and C.2.7(3)(a), pp.134,146.
-/


public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

theorem normal_component_chiZero_of_sylow_control
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (T : Sylow 2 G) (M : Subgroup G)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ K ≤ M) : IsChiZeroBlockIn K := by
  classical
  obtain ⟨r,hr,L,hL,houtL,hm,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple hG hf T M hcpu
  have hLK (i) : L i ≤ K :=
    (le_pResidual_of_isPPerfect (L i) (hL i).1.short.twoPerfect).trans
      (sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top K (T : Subgroup G) T.isPGroup' hgen⟩)
  by_contra hn
  have hne (i) : L i ≠ K := fun he => hn (he ▸ hL i)
  have hrad (i) : L i ≤ solvableRadical G := by
    have hp : (L i).subgroupOf K ≠ ⊤ := fun he =>
      hne i (le_antisymm (hLK i) (subgroupOf_eq_top.mp he))
    have hh := hK.le_solvableRadical_of_subnormal_proper (hL i).1.subnormal.subgroupOf hp
    have hh' := map_mono (f := K.subtype) hh
    rw [map_subgroupOf_eq_of_le (hLK i)] at hh'
    exact hh'.trans (map_solvableRadical_subtype_le_of_normal K)
  have hKN : ¬ K ≤ solvableRadical G := fun hh =>
    hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective (inclusion_injective hh))
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hQN : pCore 2 G ≤ solvableRadical G :=
    le_solvableRadical _ inferInstance inferInstance
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    have hQ : pCore 2 G = ⊥ := le_bot_iff.mp (ht ▸ pCore_isPGroup.le_sylow_of_normal T)
    have htriv : (⊤ : Subgroup G) ≤ pCore 2 G := by
      rw [←hf]
      intro x _
      apply centralizer_generalizedFitting_le G
      rw [hf,hQ]
      intro y hy
      simp only [mem_bot.mp hy,one_mul,mul_one]
    exact hK.ne_bot (le_bot_iff.mp ((le_top : K ≤ ⊤).trans (hQ ▸ htriv)))
  let q := QuotientGroup.mk' (solvableRadical G)
  have hstrict := (QuasisimpleThompson.component_thompson_intersection_control
    K (T : Subgroup G) M (solvableRadical G) hK T.isPGroup' hTne hgen
    (pCore_isPGroup.le_sylow_of_normal T) hQN hKN hcpu hout).2
  apply (not_le_of_gt hstrict)
  rintro z ⟨x,hx,rfl⟩
  obtain ⟨m,b,he⟩ := hprod x
  have hpK : (List.ofFn (fun i => (b i : G))).prod ∈ K :=
    K.list_prod_mem (fun a ha => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact hLK i (b i).property)
  have hpN : (List.ofFn (fun i => (b i : G))).prod ∈ solvableRadical G :=
    (solvableRadical G).list_prod_mem (fun a ha => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact hrad i (b i).property)
  have hmK : (m : G) ∈ K := by
    have hh := K.mul_mem hx (K.inv_mem hpK)
    rw [he,mul_inv_cancel_right] at hh
    exact hh
  refine ⟨m,⟨hmK,m.property⟩,?_⟩
  change q m = q x
  rw [he,map_mul,show q (List.ofFn (fun i => (b i : G))).prod = 1 from
    (QuotientGroup.eq_one_iff _).mpr hpN,mul_one]

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {H K R M : Subgroup G}

theorem chiZero_of_sylow_normal_input
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hs : Chapter1.IsSylowIn 2 R (K ⊔ R)) :
    IsChiZeroBlockIn (K.subgroupOf (K ⊔ R)) := by
  let D := K ⊔ R
  let K₀ := K.subgroupOf D
  let R₀ := R.subgroupOf D
  let M₀ := M.subgroupOf D
  let i : D →* H := inclusion h.join_le
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ D from le_sup_left)
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hK : K₀.IsCComponent := h.component.2.subgroupOf_of_le le_sup_left h.join_le
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hG : IsSQTK KnownSimple.IsKnownSimple D :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.join_le)).mp (h.setup.sqtk.subgroup _)
  have hf : generalizedFitting D = pCore 2 D := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact centralizer_pCore_sup_le 2 K R
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.fitting) hR h.normalizes
  obtain ⟨T,hT⟩ := hs
  have hTR : (T : Subgroup D) = R₀ := by
    apply map_injective D.subtype_injective
    rw [hT,map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right)]
  have hgen : K₀ ⊔ (T : Subgroup D) = ⊤ := by
    rw [hTR,←subgroupOf_sup (show K ≤ D from le_sup_left)
      (show R ≤ D from le_sup_right),subgroupOf_self]
  have hRi : R₀.map i = R.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hx; exact ⟨⟨x,mem_sup_right hx⟩,hx,rfl⟩
  have hcontrol : (T : Subgroup D).characteristicNormalizerClosure ≤ M₀ := by
    rw [hTR]
    intro x hx
    have hh := map_characteristicNormalizerClosure_le i (inclusion_injective h.join_le) R₀
    rw [hRi] at hh
    exact h.setup.characteristic_control (hh (mem_map_of_mem i hx))
  have hout : ¬ K₀ ≤ M₀ := fun hh => h.outside
    (fun k hk => hh (show (⟨k,mem_sup_left hk⟩ : D) ∈ K₀ from hk))
  exact normal_component_chiZero_of_sylow_control hG hf K₀ hK T M₀ hgen hcontrol hout


theorem source_chiZero_of_sylow_input
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hs : Chapter1.IsSylowIn 2 R (K ⊔ R)) :
    IsBlock (K.subgroupOf H) ∧ IsChiZeroBlock K := by
  have hb := chiZero_of_sylow_normal_input h hs
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)
  have hshort : IsShort K := RankOne.Solvable.isShort_of_equiv e hb.1.short
  exact ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv
    (subgroupOfEquivOfLe h.component.1).symm hshort,h.component.2.subnormal⟩,
    hb.2.of_mulEquiv e⟩

end CFSG.Quasithin.ChapterC.C27Source
