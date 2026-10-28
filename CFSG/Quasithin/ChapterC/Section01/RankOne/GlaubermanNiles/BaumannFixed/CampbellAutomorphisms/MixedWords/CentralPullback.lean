module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.CentralBounds
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.NaturalTransport

/-!
# CentralPullback for Campbell mixed words

If a commutator between a transported F-layer and a submaximal core group is central, and its inverse Sylow image is central too, the natural fixed-point lifting theorem kills it. This is the precise transported displacement argument in Campbell II.6.4(d).
Source: Campbell, Pushing up in Finite Groups, II.6.4, printed p.32.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.automorphism_conjugate_commutes_of_central_pullback
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S) (g : H)
    (Y : Subgroup H) (hY : ∃ A ∈ elementaryAbelianMaxSubgroups S, Y ≤ A)
    (hYQ : Y ≤ pCore 2 H)
    (hCS : ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆ ≤ S)
    (hC : ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆ ≤ center H)
    (hCi : automorphismImage S a.symm
      ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆ ≤ center H) :
    ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply h.automorphism_conjugate_centralizes_of_natural S hB a g Y hY hYQ
  intro y hy x hx
  obtain ⟨x',⟨x'',⟨v,hv,rfl⟩,rfl⟩,rfl⟩ := hx
  let c := MulAut.conj g
  have hxF : c (a v) ∈ (automorphismImage S a (Campbell.F H)).map c.toMonoidHom :=
    mem_map_of_mem c.toMonoidHom (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom (Campbell.V_le_F hv)))
  let u := ⁅y,c (a v)⁆
  have hu := commutator_mem_commutator hy hxF
  have huc : u ∈ center H := hC hu
  have hy0Q : c.symm y ∈ pCore 2 H := by
    change g⁻¹*y*g ∈ pCore 2 H
    simpa only [inv_inv] using (inferInstance : (pCore 2 H).Normal).conj_mem y (hYQ hy) g⁻¹
  let t : S := ⟨c.symm y,hQS hy0Q⟩
  let us : S := ⟨u,hCS hu⟩
  have hcu : c.symm u=u := by
    change g⁻¹*u*g=u
    rw [mem_center_iff.mp huc g⁻¹,inv_mul_cancel_right]
  have hword : ⁅t,a v⁆=us := by
    apply Subtype.ext
    have he := map_commutatorElement c.symm.toMonoidHom y (c (a v))
    change c.symm ⁅y,c (a v)⁆ = ⁅c.symm y,c.symm (c (a v))⁆ at he
    rw [c.symm_apply_apply] at he
    exact he.symm.trans hcu
  have him : (a.symm us:H) ∈ automorphismImage S a.symm ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆ :=
    mem_map_of_mem S.subtype (mem_map_of_mem a.symm.toMonoidHom hu)
  have hcomm : ⁅(a.symm t:H),(v:H)⁆ ∈ center H := by
    have he := congrArg a.symm hword
    rw [map_commutatorElement,a.symm_apply_apply] at he
    have he' : ⁅(a.symm t:H),(v:H)⁆=(a.symm us:H) := congrArg Subtype.val he
    rw [he']
    exact hCi him
  have hone := h.central_campbell_displacement_eq_one hB (a.symm t) v hv hcomm
  have he : ⁅a.symm t,v⁆=1 := Subtype.ext hone
  have he' := congrArg a he
  rw [map_commutatorElement,a.apply_symm_apply,map_one,hword] at he'
  have huone : u=1 := congrArg Subtype.val he'
  exact (commutatorElement_eq_one_iff_mul_comm.mp huone).symm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
