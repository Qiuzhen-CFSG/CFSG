module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SylowBlocks
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRadical

/-!
# The C.2.5 normal component without an extra quasisimplicity premise

The existing Sylow-block theorem handles a component whose two-core
quotient is quasisimple. In the other branch, A.3.6 makes the original
component's solvable radical prime to three. The C.1.29 ordered product
contains a χ₀ block inside the component. A proper subnormal subgroup of
a C-component lies in its solvable radical, whereas every χ₀ block has
order divisible by three. Thus this selected block is the whole component.

The source setup theorem restricts the literal C.2.3 data to KR and is
consumed in the Sylow branch of original15.2.4, printed p.1106.
-/

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
public theorem normal_component_chiZero_of_sylow_control_unrestricted
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    (T : Sylow 2 G) (M : Subgroup G)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ K ≤ M) : IsChiZeroBlockIn K := by
  classical
  by_cases hq : IsQuasisimple (K ⧸ pCore 2 K)
  · let := hq
    exact normal_component_chiZero_of_sylow_control hG hf K hK T M hgen hcpu hout
  have hrad3 := ChapterA.Section03.cComponent_radical_primeTo_three_of_not_quasisimple hG hK hq
  obtain ⟨r,hr,L,hL,houtL,hm,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple hG hf T M hcpu
  have hLK (i) : L i ≤ K :=
    (le_pResidual_of_isPPerfect (L i) (hL i).1.short.twoPerfect).trans
      (sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top K (T : Subgroup G) T.isPGroup' hgen⟩)
  have hex : ∃ i : Fin r, L i = K := by
    by_contra hn
    have hnone : ∀ i, L i ≠ K := by simpa using hn
    have hzero : r = 0 := by
      by_contra hr0
      let i : Fin r := ⟨0,Nat.pos_of_ne_zero hr0⟩
      have hp : (L i).subgroupOf K ≠ ⊤ := fun he =>
        hnone i (le_antisymm (hLK i) (subgroupOf_eq_top.mp he))
      have hrad := hK.le_solvableRadical_of_subnormal_proper (hL i).1.subnormal.subgroupOf hp
      have hc : 3 ∣ Nat.card ((L i).subgroupOf K) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe (hLK i)).toEquiv]
        exact RankOne.ChiProduct.three_dvd_card_of_chi (hL i).2.chi
      exact hrad3 (hc.trans (card_dvd_of_le hrad))
    subst r
    apply hout
    intro x hx
    obtain ⟨m,b,he⟩ := hprod x
    have he' : x = (m : G) := by simpa using he
    exact he' ▸ m.property
  obtain ⟨i,hi⟩ := hex
  exact hi ▸ hL i

/-- C.2.5 applied to a normalizing C-component, with no prior assumption on
its two-core quotient. -/
public theorem chiZero_of_sylow_setup
    {H K R M : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H R M)
    (hcomp : K ∈ Chapter1.cComponentsIn H)
    (hfitting : generalizedFitting K = pCore 2 K)
    (hout : ¬ K ≤ M) (hnorm : R ≤ normalizer (K : Set G))
    (hs : Chapter1.IsSylowIn 2 R (K ⊔ R)) : IsChiZeroBlock K := by
  let D := K ⊔ R
  let K₀ := K.subgroupOf D
  let R₀ := R.subgroupOf D
  let M₀ := M.subgroupOf D
  have hDH : D ≤ H := sup_le hcomp.1 hsetup.radical_le
  let i : D →* H := inclusion hDH
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hnorm)
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ D from le_sup_left)
  have hK : K₀.IsCComponent := hcomp.2.subgroupOf_of_le le_sup_left hDH
  have hR : IsPGroup 2 R := by
    have hh := hsetup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le hsetup.radical_le] at hh
  have hG : IsSQTK KnownSimple.IsKnownSimple D :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hDH)).mp (hsetup.sqtk.subgroup _)
  have hf : generalizedFitting D = pCore 2 D := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact centralizer_pCore_sup_le 2 K R
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfitting) hR hnorm
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
    have hh := map_characteristicNormalizerClosure_le i (inclusion_injective hDH) R₀
    rw [hRi] at hh
    exact hsetup.characteristic_control (hh (mem_map_of_mem i hx))
  have hout' : ¬ K₀ ≤ M₀ := fun hh => hout
    (fun k hk => hh (show (⟨k,mem_sup_left hk⟩ : D) ∈ K₀ from hk))
  exact (normal_component_chiZero_of_sylow_control_unrestricted hG hf K₀ hK T M₀
    hgen hcontrol hout').2.of_mulEquiv e
end CFSG.Quasithin.ChapterC.C27Source
