module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.CentralBounds
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.NaturalTransport

/-!
# Two fixed-layer bounds kill the mixed displacement

When both inverse automorphisms keep V in the two-core, comparison makes
both transported fixed layers central in H. A commutator in the original
and transported fixed layers pulls back to a central displacement on the
actual natural V. Fixed-point lifting kills that displacement, and
submaximal replacement upgrades natural centralization to all of F.
Source: Campbell II.6.4(c,d), printed p.32, in its Aut(S) application.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.automorphism_conjugate_commutes_of_double_fixed
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S) (g : H)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (Y : Subgroup H) (hY : ∃ A ∈ elementaryAbelianMaxSubgroups S, Y ≤ A)
    (hYQ : Y ≤ pCore 2 H)
    (hb : ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆ ≤
      automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) ⊓
        (Campbell.V H ⊓ centralizer (S : Set H))) :
    ⁅Y,(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  have hz := h.automorphism_fixed_le_center S hB a (hAll a) hF
  have hzi := h.automorphism_fixed_le_center S hB a.symm (hAll a.symm)
    (h.automorphism_F_inverse_not_le S a hF)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply h.automorphism_conjugate_centralizes_of_natural S hB a g Y hY hYQ
  intro y hy x hx
  obtain ⟨x',⟨x'',⟨v,hv,rfl⟩,rfl⟩,rfl⟩ := hx
  let c := MulAut.conj g
  have hxF : c (a v) ∈ (automorphismImage S a (Campbell.F H)).map c.toMonoidHom :=
    mem_map_of_mem c.toMonoidHom (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom (Campbell.V_le_F hv)))
  let u := ⁅y,c (a v)⁆
  have hu := hb (commutator_mem_commutator hy hxF)
  have huc : u ∈ center H := hz hu.1
  have hy0Q : c.symm y ∈ pCore 2 H := by
    change g⁻¹*y*g ∈ pCore 2 H
    simpa only [inv_inv] using (inferInstance : (pCore 2 H).Normal).conj_mem y (hYQ hy) g⁻¹
  let t : S := ⟨c.symm y,hQS hy0Q⟩
  let us : S := ⟨u,hVS hu.2.1⟩
  have hcu : c.symm u=u := by
    change g⁻¹*u*g=u
    rw [mem_center_iff.mp huc g⁻¹,inv_mul_cancel_right]
  have hword : ⁅t,a v⁆=us := by
    apply Subtype.ext
    have he := map_commutatorElement c.symm.toMonoidHom y (c (a v))
    change c.symm ⁅y,c (a v)⁆ = ⁅c.symm y,c.symm (c (a v))⁆ at he
    rw [c.symm_apply_apply] at he
    exact he.symm.trans hcu
  have him : (a.symm us:H) ∈ automorphismImage S a.symm (Campbell.V H ⊓ centralizer (S : Set H)) :=
    mem_map_of_mem S.subtype (mem_map_of_mem a.symm.toMonoidHom hu.2)
  have hcomm : ⁅(a.symm t:H),(v:H)⁆ ∈ center H := by
    have he := congrArg a.symm hword
    rw [map_commutatorElement,a.symm_apply_apply] at he
    have he' : ⁅(a.symm t:H),(v:H)⁆=(a.symm us:H) := congrArg Subtype.val he
    rw [he']
    exact hzi him
  have hone := h.central_campbell_displacement_eq_one hB (a.symm t) v hv hcomm
  have he : ⁅a.symm t,v⁆=1 := Subtype.ext hone
  have he' := congrArg a he
  rw [map_commutatorElement,a.apply_symm_apply,map_one,hword] at he'
  have huone : u=1 := congrArg Subtype.val he'
  exact (commutatorElement_eq_one_iff_mul_comm.mp huone).symm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
