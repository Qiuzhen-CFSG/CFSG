module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.Escape

/-!
# NaturalTransport for Campbell mixed words

Transport submaximal replacement through the actual Sylow automorphism and ambient conjugation. Centralizing its natural V-layer forces centralization of the full F-layer; the proof uses the literal inverse maps, without extending a Sylow automorphism to H. Source: Campbell II.4.4 and II.6.4, pp.25 and32.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.automorphism_conjugate_centralizes_of_natural
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S) (g : H)
    (Y : Subgroup H) (hY : ∃ A ∈ elementaryAbelianMaxSubgroups S, Y ≤ A)
    (hYQ : Y ≤ pCore 2 H)
    (hc : Y ≤ centralizer ((automorphismImage S a (Campbell.V H)).map
      (MulAut.conj g).toMonoidHom : Set H)) :
    Y ≤ centralizer ((automorphismImage S a (Campbell.F H)).map
      (MulAut.conj g).toMonoidHom : Set H) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans hQS
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  let c := MulAut.conj g
  let Y0 := Y.map c.symm.toMonoidHom
  let Y1 := automorphismImage S a.symm Y0
  have hci : c.symm.toMonoidHom=(MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp [c]
  obtain ⟨A,hA,hAQ,hYA⟩ := h.submaximal_core_conjugate S hB Y hY hYQ g⁻¹
  have hY0S : Y0 ≤ S := by change Y.map c.symm.toMonoidHom ≤ S; rw [hci]; exact hYA.trans hA.1
  have hY1A : Y1 ≤ automorphismImage S a.symm A := automorphismImage_mono S a.symm (by change Y.map c.symm.toMonoidHom ≤ A; rwa [hci])
  have hsplit := (h.campbellF_submaximal_control hB m d Y1 (automorphismImage S a.symm A)
    (hSd.symm ▸ automorphismImage_maxElementary S a.symm A hA) hY1A).2
  have hvcomm : Campbell.V H ≤ centralizer (Y1 : Set H) := by
    intro v hv z hz
    obtain ⟨z',⟨t,ht,rfl⟩,rfl⟩ := hz
    obtain ⟨y,hy,hey⟩ := ht
    change c.symm y=(t:H) at hey
    let vs : S := ⟨v,hVS hv⟩
    have hm : c (a vs) ∈ (automorphismImage S a (Campbell.V H)).map c.toMonoidHom :=
      mem_map_of_mem c.toMonoidHom (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hv))
    have hh := hc hy _ hm
    have hh0 := congrArg c.symm hh
    have hc0 : (a vs:H)*(t:H)=(t:H)*(a vs:H) := by
      simpa only [map_mul,c.symm_apply_apply,hey] using hh0
    have hc1 : a vs*t=t*a vs := Subtype.ext hc0
    have hh1 := congrArg a.symm hc1
    have he : vs*a.symm t=a.symm t*vs := by
      simpa only [map_mul,a.symm_apply_apply] using hh1
    exact (congrArg Subtype.val he).symm
  have hFC : Campbell.F H ≤ centralizer (Y1 : Set H) := by
    rw [hsplit]
    exact sup_le hvcomm inf_le_right
  intro y hy x hx
  obtain ⟨x',⟨x'',⟨f,hf,rfl⟩,rfl⟩,rfl⟩ := hx
  let t : S := ⟨c.symm y,hY0S (mem_map_of_mem c.symm.toMonoidHom hy)⟩
  have ht : (a.symm t:H) ∈ Y1 :=
    mem_map_of_mem S.subtype (mem_map_of_mem a.symm.toMonoidHom
      (mem_map_of_mem c.symm.toMonoidHom hy))
  have hh : a.symm t*f=f*a.symm t := Subtype.ext (hFC hf _ ht)
  have hh' := congrArg a hh
  have he : t*a f=a f*t := by simpa only [map_mul,a.apply_symm_apply] using hh'
  have he' := congrArg (fun x : S => c (x:H)) he
  change c (a f)*y=y*c (a f)
  have htcy : c (t:H)=y := c.apply_symm_apply y
  simpa only [Subgroup.coe_mul,map_mul,htcy] using he'.symm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
