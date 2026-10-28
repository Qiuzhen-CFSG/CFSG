module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.SylowActorGeometry
/-!
# A noncommuting conjugate pair forces the transported actor to move F

If F centralizes X=(b⁻¹c_u b)⁻¹(V), applying the actual restricted α map
shows F^α centralizes (V^α)^(u⁻¹). Its maximum elementary replacement in
the core then upgrades natural centralization to the whole F-conjugate,
contradicting the given noncommuting pair. The proof retains the original
restricted automorphism and performs no extension to the ambient group.
Source: Campbell II.6.3, printed pp.30–31.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H H' : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group H'] [Finite H']
  {e : B →* H} {e' : B →* H'}
omit [Finite B] [Finite H] in
private theorem marking_transfer (h' : InLocalClass e')
    (d : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H)
    (d' : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H')
    (hd : d.marking = e.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype)
    (hd' : d'.marking = e'.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype)
    (X : Subgroup H') (hX : X ≤ d'.marking.range) :
    d.transfer d' X = (X.comap e').map e := by
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨j.val,?_,?_⟩
    · change e' j.val ∈ X
      change d'.marking j ∈ X at hj
      rwa [hd'] at hj
    · rw [hd]; rfl
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨j,hj⟩ := hX hb
    have hjb : (j : B)=b := h'.injective (by simpa only [hd',MonoidHom.comp_apply,coe_subtype] using hj)
    refine ⟨j,?_,?_⟩
    · change d'.marking j ∈ X
      rw [hj]
      exact hb
    · rw [hd]
      change e j.val = e b
      rw [hjb]


theorem InLocalClass.original_conjugate_centralizes_of_natural (h : InLocalClass e) (h' : InLocalClass e')
    (hB : IsBaumannFixed B) (Y A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups e.range) (hYA : Y ≤ A) (hAQ : A ≤ pCore 2 H) (g:H)
    (hc : Y ≤ centralizer ((((Campbell.V H').comap e').map e).map (MulAut.conj g).toMonoidHom : Set H)) :
    Y ≤ centralizer ((((Campbell.F H').comap e').map e).map (MulAut.conj g).toMonoidHom : Set H) := by
  obtain ⟨d,hd,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨d',hd',_⟩ := h'.exists_campbellEmbedding hB
  obtain ⟨n',hn',F',_,_,_,hcard',⟨m'⟩⟩ := h'.natural
  have ht := h'.campbell_marked_containments hB d'
  have htf := marking_transfer h' d d' hd hd' _ ht.1
  have htv := marking_transfer h' d d' hd hd' _ ht.2.1
  have hh := h'.paired_conjugate_centralizes_of_natural hB m' d d' Y A
    (hS ▸ hA) hYA hAQ g (by rwa [htv])
  rwa [htf] at hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem transfer_sylow_aut (a : MulAut S) (X : Subgroup H) :
    (X.comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype =
      automorphismImage S a X := by
  rw [←comap_comap,comap_equiv_eq_map_symm']
  rfl

theorem InLocalClass.actor_moves_of_conjugates_noncommute (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    let Y := automorphismImage S a (Campbell.F H)
    let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    ∀ b : W' ≃* W,
      (∀ w : W', (b w : H) = (a ⟨w,automorphismImage_le S a.symm W w.property⟩ : H)) →
      ∀ u : normalizer (W : Set H),
        ¬ Y ≤ centralizer (Y.map (MulAut.conj (u:H)⁻¹).toMonoidHom : Set H) →
        ¬ Campbell.F H ≤ centralizer (spanNaturalActor W W' b u : Set H) := by
  dsimp only
  let Y := automorphismImage S a (Campbell.F H)
  let K := Campbell.J (⊤ : Subgroup H)
  let W := conjugateSpanBy Y K
  let W' := automorphismImage S a.symm W
  intro b hb u hn hc
  have hs := h.sylow_automorphism_span S hB a hV
  have hFr := hs.2.2.2.2.2
  have hVr : Campbell.V H ≤ W' := Campbell.V_le_F.trans hFr
  have hYNat : Y ≤ centralizer ((automorphismImage S a (Campbell.V H)).map
      (MulAut.conj (u:H)⁻¹).toMonoidHom : Set H) := by
    rintro r ⟨ar,⟨r0,hr0,har⟩,rfl⟩
    subst ar
    rintro z ⟨v,⟨av,⟨v0,hv0,hav⟩,hev⟩,rfl⟩
    subst av
    subst v
    let r' : W' := ⟨r0,hFr hr0⟩
    let v' : W' := ⟨v0,hVr hv0⟩
    let x : W' := b.symm ((W.normalizerMonoidHom u).symm (b v'))
    have hfx : spanConjugationMap W W' b u x=(v':H) := by
      change (b.symm (W.normalizerMonoidHom u (b x)) : H)=(v':H)
      simp [x]
    have hxX : (x:H) ∈ spanNaturalActor W W' b u := by
      refine ⟨x,?_,rfl⟩
      change spanConjugationMap W W' b u x ∈ Campbell.V H
      rw [hfx]
      exact hv0
    have he : x*r'=r'*x := Subtype.ext (hc hr0 x hxX)
    have hbcomm := congrArg (fun w : W' => (b w:H)) he
    have hbx : (b x:H)=(u:H)⁻¹*(a v0:H)*(u:H) := by
      have hxe : b x=(W.normalizerMonoidHom u).symm (b v') := b.apply_symm_apply _
      rw [hxe]
      change (u:H)⁻¹*(b v':H)*((u:H)⁻¹)⁻¹=_
      rw [hb v',inv_inv]
    have hbr : (b r':H)=(a r0:H) := hb r'
    change (u:H)⁻¹*(a v0:H)*((u:H)⁻¹)⁻¹*(a r0:H)=(a r0:H)*((u:H)⁻¹*(a v0:H)*((u:H)⁻¹)⁻¹)
    simpa only [map_mul,Subgroup.coe_mul,hbx,hbr,inv_inv] using hbcomm
  obtain ⟨d,_,hSd⟩ := h.exists_campbellEmbedding hB
  obtain ⟨A,hA,hFA⟩ := h.campbellF_le_some_maxElementary hB d
  have hSd' : (d.sylow:Subgroup H)=S := hSd.trans (range_subtype S)
  rw [hSd'] at hA
  let B0 := automorphismImage S a A
  have hB0 := automorphismImage_maxElementary S a A hA
  let E0 := (B0 ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H)
  have hE0 := h.omegaCore_replacement_maximal hB d B0 (by rw [hSd']; exact hB0)
  have hE0Q : E0 ≤ pCore 2 H := sup_le inf_le_right
    (fun z hz => ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hYE0 : Y ≤ E0 := (le_inf (automorphismImage_mono S a hFA)
    ((le_conjugateSpanBy Y K).trans hs.1)).trans le_sup_left
  have h' := h.precomp_equiv a.symm
  have hout := h.original_conjugate_centralizes_of_natural h' hB Y E0
    (by rwa [hSd] at hE0) hYE0 hE0Q (u:H)⁻¹
    (by simpa only [transfer_sylow_aut] using hYNat)
  exact hn (by simpa only [transfer_sylow_aut] using hout)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
