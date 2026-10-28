module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.OriginalSpans
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public import Theory.GroupTheory.SubgroupAutomorphismImages
/-!
# Campbell's involution theorem for the actual Sylow automorphism

Let α be an automorphism of the original Sylow subgroup S and assume
V^α≤O₂(H). Form W=⟨(F^α)^J(H)⟩ and its literal inverse image W′=W^(α⁻¹).
Both are normalized by S. The paired comparison theorem gives the core
and Frattini bounds and, in the noncontainment case, centrality of Z^α.
Injective Frattini transport places Φ(W′) inside V.

The final theorem constructs the restricted equivalence b:W′≃W and proves
[h,h^g]=1 for every involution h∈W and every g in the inverse image of V
under b⁻¹ c_u b, where u∈J(H). This is precisely the transported natural
actor in Campbell II.6.2, with the original automorphism recorded by an
elementwise identity. The involution, cross-normalizer, Frattini and
natural-displacement premises are all discharged. The F^α≤F case follows
from the elementary structure of W. No extension of α to H is assumed.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.6.1–2,
printed pp.29–30, specialized to Aut(S) as required by Corollary 1 and C.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem transfer_sylow_aut (a : MulAut S) (X : Subgroup H) :
    (X.comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype =
      automorphismImage S a X := by
  rw [←comap_comap,comap_equiv_eq_map_symm']
  rfl

omit [Finite H] in
private theorem inverse_marking_range (a : MulAut S) :
    (S.subtype.comp a.symm.toMonoidHom).range=S := by
  rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.symm.surjective,
    ←MonoidHom.range_eq_map,range_subtype]

theorem InLocalClass.sylow_automorphism_span (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    let Y := automorphismImage S a (Campbell.F H)
    let Z := automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H))
    let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    W ≤ pCore 2 H ∧ S ≤ normalizer (W : Set H) ∧ S ≤ normalizer (W' : Set H) ∧
      (frattini W).map W.subtype ≤ Z ∧
      (frattini W').map W'.subtype ≤ Campbell.V H ∧ Campbell.F H ≤ W' := by
  let Y := automorphismImage S a (Campbell.F H)
  let Z0 := Campbell.V H ⊓ centralizer (S : Set H)
  let Z := automorphismImage S a Z0
  let K := Campbell.J (⊤ : Subgroup H)
  let W := conjugateSpanBy Y K
  let W' := automorphismImage S a.symm W
  have h' := h.precomp_equiv a.symm
  have hv : ((Campbell.V H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ pCore 2 H := by
    rwa [transfer_sylow_aut]
  have hs := h.original_span_core_frattini h' hB hv
  dsimp only at hs
  rw [transfer_sylow_aut,transfer_sylow_aut,inverse_marking_range] at hs
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans hQS
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  have hWQ : W ≤ pCore 2 H := hs.1.trans (sSup_le fun _ hA => hA.1)
  have hWS : W ≤ S := hWQ.trans hQS
  have hYN : S ≤ normalizer (Y : Set H) :=
    le_normalizer_automorphismImage S a (Campbell.F H) hFS
      (by let : (Campbell.F H).Normal := Campbell.F_normal; exact le_normalizer_of_normal)
  have hKN : S ≤ normalizer (K : Set H) := by
    let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic := elementaryAbelianMaxJ_top_characteristic
    change S ≤ normalizer (elementaryAbelianMaxJ (⊤ : Subgroup H) : Set H)
    exact le_normalizer_of_normal
  have hWN : S ≤ normalizer (W : Set H) :=
    (le_inf hYN hKN).trans (normalizer_inf_le_normalizer_conjugateSpan Y K)
  have hWN' : S ≤ normalizer (W' : Set H) := le_normalizer_automorphismImage S a.symm W hWS hWN
  have hPhi' : (frattini W').map W'.subtype ≤ Campbell.V H := by
    rw [frattini_automorphismImage S a.symm W hWS]
    have hh := automorphismImage_mono S a.symm hs.2.2
    rw [automorphismImage_symm S a Z0 (inf_le_left.trans hVS)] at hh
    exact hh.trans inf_le_left
  have hFW' : Campbell.F H ≤ W' := by
    have hh := automorphismImage_mono S a.symm (le_conjugateSpanBy Y K)
    rw [automorphismImage_symm S a (Campbell.F H) hFS] at hh
    exact hh
  exact ⟨hWQ,hWN,hWN',hs.2.2,hPhi',hFW'⟩

theorem InLocalClass.sylow_automorphism_fixed_central (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬ automorphismImage S a (Campbell.F H) ≤ Campbell.F H) :
    automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) ≤
      centralizer (Campbell.J (⊤ : Subgroup H) : Set H) := by
  have h' := h.precomp_equiv a.symm
  have hv : ((Campbell.V H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ pCore 2 H := by
    rwa [transfer_sylow_aut]
  have hf : ¬ ((Campbell.F H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ Campbell.F H := by
    rwa [transfer_sylow_aut]
  have hc := h.campbell_comparison_original_markings h' hB hv hf
  rw [inverse_marking_range,transfer_sylow_aut] at hc
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hfix := h.sylow_fixed_eq_commutator hB m d hS
  rw [←h.campbellV_eq_moved hB m] at hfix
  have hS' : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hSet : (d.sylow : Set H)=(S : Set H) := congrArg (fun X : Subgroup H => (X : Set H)) hS'
  rw [hSet,hS'] at hfix
  rw [hfix]
  intro z hz
  obtain ⟨x,hx,rfl⟩ := hc hz
  intro k hk
  exact congrArg Subtype.val ((mem_center_iff.mp hx) (⟨k,hk⟩ : Campbell.J (⊤ : Subgroup H)))
end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.sylow_automorphism_involutions (hL : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    let W := conjugateSpanBy (automorphismImage S a (Campbell.F H)) (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    ∃ b : W' ≃* W,
      (∀ w : W', (b w : H) = (a ⟨w,automorphismImage_le S a.symm W w.property⟩ : H)) ∧
      ∀ u : normalizer (W : Set H), (u : H) ∈ Campbell.J (⊤ : Subgroup H) →
        ∀ g : W', spanConjugationMap W W' b u g ∈ Campbell.V H →
          ∀ x ∈ W, x^2=1 → ⁅x,(g:H)*x*(g:H)⁻¹⁆=1 := by
  let Y := automorphismImage S a (Campbell.F H)
  let Z := automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H))
  let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
  let W' := automorphismImage S a.symm W
  have hs := hL.sylow_automorphism_span S hB a hV
  obtain ⟨T,hT,_⟩ := hL.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hWS : W ≤ S := hs.1.trans hQS
  have hW'S : W' ≤ S := automorphismImage_le S a.symm W
  let c := automorphismImageEquiv S a.symm W hWS
  let b : W' ≃* W := c.symm
  refine ⟨b,?_,?_⟩
  · intro w
    have hc := automorphismImageEquiv_apply S a.symm W hWS (b w)
    have he : (a.symm ⟨b w,hWS (b w).property⟩ : H)=(w:H) := by
      rw [←hc]
      exact congrArg Subtype.val (c.apply_symm_apply w)
    have he' : a.symm ⟨b w,hWS (b w).property⟩=⟨w,hW'S w.property⟩ := Subtype.ext he
    exact congrArg Subtype.val ((a.apply_symm_apply ⟨b w,hWS (b w).property⟩).symm.trans (congrArg a he'))
  · intro u hu g hg x hx hx2
    have hgN : (g:H) ∈ normalizer (W : Set H) := hs.2.1 (hW'S g.property)
    have hxN : x ∈ normalizer (W' : Set H) := hs.2.2.1 (hWS hx)
    by_cases hF : Y ≤ Campbell.F H
    · have hWF : W ≤ Campbell.F H :=
        conjugateSpanBy_le hF (by let : (Campbell.F H).Normal := Campbell.F_normal; exact le_normalizer_of_normal)
      let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
      let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWF
      have hxg : (g:H)*x*(g:H)⁻¹ ∈ W := (mem_normalizer_iff.mp hgN x).mp hx
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) ⟨(g:H)*x*(g:H)⁻¹,hxg⟩)
    · have hWp : IsPGroup 2 W := pCore_isPGroup.of_injective (inclusion hs.1) (inclusion_injective hs.1)
      have hW'p : IsPGroup 2 W' := hWp.of_equiv c
      have hZ := hL.sylow_automorphism_fixed_central S hB a hV hF
      have hg2 : g^2=1 := by
        have hf : Function.Injective (spanConjugationMap W W' b u) := W'.subtype_injective.comp
          (((b.trans (W.normalizerMonoidHom u)).trans b.symm).injective)
        apply hf
        rw [map_pow,map_one]
        let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) := omegaOneCenterAmbient_elementaryAbelian _
        exact elemPow_eq_one_of_isElementaryAbelian _ (Campbell.V_le_omegaCore hg)
      exact hL.involution_conjugate_commutes_of_span_transport hB W W' Z hWp hW'p b u hu hZ
        hs.2.2.2.1 hs.2.2.2.2.1 g x hg2 hx2 hx hgN hxN hg
end CFSG.Quasithin.ChapterC.GlaubermanNiles
