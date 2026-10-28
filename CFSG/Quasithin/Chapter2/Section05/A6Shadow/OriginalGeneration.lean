module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Source
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.MaximalTransport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry

/-!
# Marked centralizer generation in the original A₆ source

The faithful crossing-core action and the exact involution fixed-group criterion
identify the only core involution whose crossing centralizer could lie in S.
The actual compatible action also proves C_H(tˣ) = S, while the model Sylow
maximality pulls back to H. The two crossed involution centralizers therefore
generate H and normalize the crossed component. The existing quasithin
obstruction to commuting A₆ components proves rank one of the original core.

Only componenthood in the other core-involution centralizers remains explicit;
this is the genuine preceding overcomponent claim of source 2.5.26. All
marked-model, maximality, quotient and crossing premises are constructed from
the original tuple. Right conjugation is retained by using x⁻¹ in the existing
generation theorem.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
2.5.26, printed p.569, final paragraph.
-/

public section
open Subgroup Theory.GroupTheory AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
open ElementaryCore
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

private theorem action_fixed_le_image (d : EarlierSetup κ G) (a : d.H)
    (h : d.K ⊓ centralizer ({(a : G)} : Set G) ≤ d.S) :
    (GLS3.Chapter5.automorphismFixedSubgroup (d.action a)).map
      (MulAut.conj : A6 →* AutA6) ≤ d.imageSylow := by
  rintro _ ⟨k,hk,rfl⟩
  change d.action a k = k at hk
  let b := d.modelK.symm k
  have hbC : (b : G) ∈ centralizer ({(a : G)} : Set G) :=
    (d.action_fixed_iff_centralizes a b).mp (by
      simpa only [b, d.modelK.apply_symm_apply] using hk)
  have hbS := h ⟨b.property,hbC⟩
  rw [d.imageSylow_eq_range]
  refine ⟨⟨b,hbS⟩, ?_⟩
  change d.action ⟨b,d.s_le_h hbS⟩ = MulAut.conj k
  rw [d.action_on_K b]
  exact congrArg MulAut.conj (d.modelK.apply_symm_apply k)

private theorem crossed_involution_fixed_not_le (d : EarlierSetup κ G)
    (htx : d.x⁻¹ * d.t * d.x = d.zK)
    (i : G) (hi : i ∈ d.SC) (hi2 : orderOf i = 2) (hit : i ≠ d.t) :
    ¬ d.K ⊓ centralizer ({d.x⁻¹ * i * d.x} : Set G) ≤ d.S := by
  classical
  let e := (MulAut.conj d.x⁻¹).subgroupMap d.SC
  let a := d.toImageSylow.comp (inclusion (d.rightConjugate_le d.sc_le_s))
  let f : d.SC →* AutA6 := (d.imageSylow : Subgroup AutA6).subtype.comp
    (a.comp e.toMonoidHom)
  have hf : Function.Injective f := Subtype.val_injective.comp
    (d.crossing_action_injective.comp e.injective)
  let iC : d.SC := ⟨i,hi⟩
  let tC : d.SC := ⟨d.t,d.t_mem⟩
  let w : d.H := ⟨e iC,
    d.s_le_h (d.rightConjugate_le d.sc_le_s (e iC).property)⟩
  have hwval : (w : G) = d.x⁻¹ * i * d.x := by
    simp only [w,e,MulEquiv.coe_subgroupMap_apply,MulAut.conj_apply,inv_inv]
    rfl
  have hfw : f iC = d.action w := rfl
  have hfo : orderOf (d.action w) = 2 := by
    rw [←hfw,orderOf_injective f hf]
    exact (orderOf_coe iC).symm.trans hi2
  intro hle
  have hcent := (involution_fixed_le_sylow_iff d.imageSylow (d.action w) hfo).mp
    (action_fixed_le_image d w (by simpa only [hwval] using hle))
  obtain ⟨b,hb,hbβ⟩ := hcent
  let k := (innerEquiv d).symm b
  have hkcent : k ∈ center (d.S ⊓ d.K : Subgroup G) :=
    (centerCongr (innerEquiv d).symm ⟨b,hb⟩).property
  have hkline : (k : G) ∈ zpowers d.zK := by
    rw [←d.center_sk,centerIn_eq_map_center]
    exact ⟨k,hkcent,rfl⟩
  have hkact : d.action ⟨k,d.k_le_h k.property.2⟩ = d.action w := by
    have he := congrArg (fun v : sylowInner d.imageSylow => ((v : d.imageSylow) : AutA6))
      ((innerEquiv d).apply_symm_apply b)
    exact he.trans hbβ
  have hkcases : (k : G) = 1 ∨ (k : G) = d.zK := by
    rw [mem_zpowers_iff_mem_range_orderOf,d.zK_order] at hkline
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hkline
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  rcases hkcases with hk1 | hkz
  · have hw1 : d.action w = 1 := hkact.symm.trans (by
      have he : (⟨k,d.k_le_h k.property.2⟩ : d.H) = 1 := Subtype.ext hk1
      rw [he,map_one])
    simp [hw1] at hfo
  · have he : f iC = f tC := by
      rw [hfw,←hkact]
      apply congrArg d.action
      apply Subtype.ext
      change (k : G) = (e tC : G)
      simpa only [e,MulEquiv.coe_subgroupMap_apply,MulAut.conj_apply,inv_inv] using hkz.trans htx.symm
    exact hit (congrArg Subtype.val (hf he))

private theorem centralizer_crossed_t (d : EarlierSetup κ G)
    (htx : d.x⁻¹ * d.t * d.x = d.zK) :
    d.H ⊓ centralizer ({d.x⁻¹ * d.t * d.x} : Set G) = d.S := by
  have hzK : d.zK ∈ d.K := by
    have hz : d.zK ∈ centerIn (d.S ⊓ d.K) := d.center_sk.symm ▸ mem_zpowers d.zK
    exact hz.1.2
  let k : d.K := ⟨d.zK,hzK⟩
  let v : d.H := ⟨d.zK,d.k_le_h hzK⟩
  have hv : d.action v = MulAut.conj (d.modelK k) := d.action_on_K k
  have ho : orderOf (d.action v) = 2 := by
    rw [hv,orderOf_injective _ inner_injective,d.modelK.orderOf_eq]
    exact (orderOf_coe k).symm.trans d.zK_order
  have hs : (d.sylow : Subgroup d.H) ≤ centralizer ({v} : Set d.H) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hz : d.zK ∈ centerIn d.S := d.center_s.symm ▸
      ((le_sup_right : zpowers d.zK ≤ zpowers d.t ⊔ zpowers d.zK) (mem_zpowers d.zK))
    exact hz.2 s (d.sylow_eq ▸ mem_map_of_mem d.H.subtype hs)
  have hk : d.action.ker ≤ (d.sylow : Subgroup d.H) := by
    have hSyl : (d.sylow : Subgroup d.H) = d.S.subgroupOf d.H := by
      rw [←d.sylow_eq,subgroupOf,comap_map_eq_self_of_injective d.H.subtype_injective]
    rw [d.action_kernel,hSyl]
    exact subgroupOf_mono d.H d.sc_le_s
  rw [htx]
  exact (A6Shadow.relative_centralizer_eq_sylow_of_inner_image d.H d.action
    d.action_surjective d.sylow hk v hs ho (hv ▸ ⟨_,rfl⟩)).trans d.sylow_eq

/-- The full marked local generation step, retaining only componenthood at
all core involutions. All quotient Sylow and fixed-subgroup premises are derived. -/
theorem EarlierSetup.rank_one_of_core_involution_components (d : EarlierSetup κ G)
    (hphi : frattini d.SC ≠ ⊥) (hGt : d.H = centralizer ({d.t} : Set G))
    (hc : ∀ i : G, i ∈ d.SC → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (d.K.subgroupOf (centralizer {i}))) :
    primeRank 2 d.SC = 1 := by
  obtain ⟨htx,_⟩ := d.involution_identities_of_frattini_ne hphi
  have htxK : MulAut.conj d.x⁻¹ d.t ∈ d.K := by
    have hh : d.zK ∈ centerIn (d.S ⊓ d.K) := d.center_sk.symm ▸ mem_zpowers d.zK
    rw [MulAut.conj_apply,inv_inv,htx]
    exact hh.1.2
  have hx2 : d.x⁻¹ * d.x⁻¹ ∈ d.S := by
    simpa only [pow_two,mul_inv_rev] using d.S.inv_mem d.square_mem
  exact A6ShadowRankOne.primeRank_eq_one_of_component_centralizers d.simpleQTKE.quasithin
    d.K d.H d.S d.SC d.t d.x⁻¹ d.modelK d.k_le_h d.s_le_h hGt
    (d.centralizer_K ▸ inf_le_right) (d.core ▸ isPGroup_pCoreIn 2 d.H)
    d.t_mem d.t_order hc
    (d.sylow_isCoatom_of_image (sylow_isCoatom d.imageSylow))
    (by simpa only [MulAut.conj_apply,inv_inv] using centralizer_crossed_t d htx)
    (by simpa only [MulAut.conj_apply,inv_inv] using crossed_involution_fixed_not_le d htx)
    htxK hx2

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini

namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement A6Shadow.Frattini A6Shadow.OriginalFrattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original 2.5.26 generation argument, with its marked model hypotheses
proved. Only componenthood at each original core involution remains explicit. -/
theorem MathieuSourceSetup.alternating_six_source_rank_one_of_components
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hc : ∀ i : G, i ∈ twoCore H → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (K.subgroupOf (centralizer {i}))) :
    primeRank 2 (twoCore H) = 1 := by
  obtain ⟨d,hH,hK,hS,hM,_,_,hSC,hGt⟩ :=
    original_earlier_setup c hG hempty hgen hb hstar eK
  have hphi := (MathieuSourceSetup.alternating_six_source_frattini_and_crossing
    c hG hempty hgen hb hstar eK).1
  have hcd : ∀ i : G, i ∈ d.SC → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (d.K.subgroupOf (centralizer {i})) := by
    intro i hi hi2
    rw [hK]
    exact hc i (hSC ▸ hi) hi2
  have hr := d.rank_one_of_core_involution_components (hSC ▸ hphi) hGt hcd
  exact (primeRank_congr 2 (MulEquiv.subgroupCongr hSC)).symm.trans hr

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
