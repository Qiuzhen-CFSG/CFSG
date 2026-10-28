module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.DoubleCentral

/-!
# Core for Campbell mixed words

Campbell II.6.4(c): the exact word α g α⁻¹ t α carries F back into the two-core. Two commutator bounds in the fixed layers first force the crossed inverse words to commute; applying the literal inverse maps identifies the centralizer of F and hence the core.
Source: Campbell, Pushing up in Finite Groups, II.6.4, printed p.32.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conjugate_twice (g : H) (hg : g^2=1) (X : Subgroup H) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom=X := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id H := by
    ext x
    change g*(g*x*g⁻¹)*g⁻¹=x
    have hgg : g*g=1 := by simpa only [pow_two] using hg
    calc
      g*(g*x*g⁻¹)*g⁻¹=(g*g)*x*(g*g)⁻¹ := by group
      _=x := by rw [hgg]; simp
  rw [he,Subgroup.map_id]

omit [Finite H] in
private theorem image_center_conj (X : Subgroup H) (hX : X ≤ center H) (g : H) :
    X.map (MulAut.conj g).toMonoidHom=X := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change g*y*g⁻¹ ∈ X
    rw [mem_center_iff.mp (hX hy) g,mul_inv_cancel_right]
    exact hy
  · intro x hx
    refine ⟨x,hx,?_⟩
    change g*x*g⁻¹=x
    rw [mem_center_iff.mp (hX hx) g,mul_inv_cancel_right]

omit [Finite H] in
private theorem order_two_power (g : H) (hg : g^2=1) : ∃n,orderOf g=2^n := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp (orderOf_dvd_of_pow_eq_one hg) with he | he
  · exact ⟨0,by simpa using he⟩
  · exact ⟨1,by simpa using he⟩

theorem InLocalClass.mixed_inverse_words_commute
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (g t : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) (ht : t ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : g^2=1) (ht2 : t^2=1) :
    ⁅(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom,
      automorphismImage S a ((automorphismImage S a.symm (Campbell.F H)).map
        (MulAut.conj t).toMonoidHom)⁆=⊥ := by
  let F := Campbell.F H
  let Z := Campbell.V H ⊓ centralizer (S : Set H)
  let X := (automorphismImage S a F).map (MulAut.conj g).toMonoidHom
  let P := automorphismImage S a.symm X
  let B := (automorphismImage S a.symm F).map (MulAut.conj t).toMonoidHom
  let Y := automorphismImage S a B
  let Pt := P.map (MulAut.conj t).toMonoidHom
  let W := automorphismImage S a Pt
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  have hFS : F ≤ S := Campbell.F_le_pCore.trans hQS
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  have hZS : Z ≤ S := inf_le_left.trans hVS
  obtain ⟨A,hA,hAQ,hXA⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
  have hXS : X ≤ S := hXA.trans hA.1
  obtain ⟨AP,hAP,hAPQ,hPAP⟩ := h.inverse_conjugate_submaximal S hB a (hAll a) g hg (order_two_power g hg2)
  have hPQ : P ≤ pCore 2 H := hPAP.trans hAPQ
  have hPS : P ≤ S := hPQ.trans hQS
  obtain ⟨AT,hAT,hATQ,hPtAT⟩ := h.submaximal_core_conjugate S hB P ⟨AP,hAP,hPAP⟩ hPQ t
  have hPtS : Pt ≤ S := hPtAT.trans hAT.1
  have hWsub : ∃ A ∈ elementaryAbelianMaxSubgroups S, W ≤ A :=
    ⟨automorphismImage S a AT,automorphismImage_maxElementary S a AT hAT,
      automorphismImage_mono S a hPtAT⟩
  have hYa : Y=automorphismImage S a.symm.symm B := by rfl
  have hYQ : Y ≤ pCore 2 H := by
    simpa only [MulEquiv.symm_symm] using
      h.inverse_conjugate_core S hB a.symm (hAll a.symm) t ht (order_two_power t ht2)
  obtain ⟨AY,hAY,hAYQ,hYAY⟩ := h.inverse_conjugate_submaximal S hB a.symm (hAll a.symm) t ht (order_two_power t ht2)
  have hYsub : ∃ A ∈ elementaryAbelianMaxSubgroups S, Y ≤ A := by
    exact ⟨AY,hAY,by simpa only [MulEquiv.symm_symm] using hYAY⟩
  have hYR : Y ≤ Campbell.J (pCore 2 H) :=
    h.submaximal_core_le_thompson hB d Y AY (hSd.symm ▸ hAY) (by simpa only [MulEquiv.symm_symm] using hYAY) hYQ
  have hfirst : ⁅X,Y⁆ ≤ automorphismImage S a Z :=
    (commutator_mono le_rfl hYR).trans (h.automorphism_conjugate_core_commutator S hB a (hAll a) g hg)
  have hsecond : ⁅X,Y⁆ ≤ Z := by
    have hWF := h.submaximal_commutator_F_le_fixed S hB W hWsub
    have hstep := automorphismImage_mono S a.symm hWF
    rw [automorphismImage_commutator S a.symm W F (automorphismImage_le S a Pt) hFS,
      automorphismImage_symm S a Pt hPtS] at hstep
    have hstep' := map_mono (f := (MulAut.conj t).toMonoidHom) hstep
    rw [map_commutator] at hstep'
    change ⁅Pt.map (MulAut.conj t).toMonoidHom,B⁆ ≤
      (automorphismImage S a.symm Z).map (MulAut.conj t).toMonoidHom at hstep'
    rw [conjugate_twice t ht2 P,image_center_conj _
      (h.automorphism_fixed_le_center S hB a.symm (hAll a.symm)
        (h.automorphism_F_inverse_not_le S a hF)) t] at hstep'
    have hstep'' := automorphismImage_mono S a hstep'
    have hBS : B ≤ S := by
      obtain ⟨AB,hAB,_,hBAB⟩ := h.automorphism_F_conjugate_submaximal S hB a.symm (hAll a.symm) t
      exact hBAB.trans hAB.1
    rw [automorphismImage_commutator S a P B hPS hBS] at hstep''
    have hPX : automorphismImage S a P=X := by
      simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm X hXS
    have hZa : automorphismImage S a (automorphismImage S a.symm Z)=Z := by
      simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm Z hZS
    rw [hPX,hZa] at hstep''
    exact hstep''
  rw [commutator_comm X Y]
  exact h.automorphism_conjugate_commutes_of_double_fixed S hB a g hAll hF Y hYsub hYQ
    (by rw [commutator_comm]; exact le_inf hfirst hsecond)

theorem InLocalClass.mixed_conjugate_core
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (g t : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) (ht : t ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : g^2=1) (ht2 : t^2=1) :
    let P := automorphismImage S a.symm
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)
    automorphismImage S a (P.map (MulAut.conj t).toMonoidHom) ≤ pCore 2 H := by
  let F := Campbell.F H
  let X := (automorphismImage S a F).map (MulAut.conj g).toMonoidHom
  let P := automorphismImage S a.symm X
  let B := (automorphismImage S a.symm F).map (MulAut.conj t).toMonoidHom
  let Y := automorphismImage S a B
  let Pt := P.map (MulAut.conj t).toMonoidHom
  let W := automorphismImage S a Pt
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  have hFS : F ≤ S := Campbell.F_le_pCore.trans hQS
  obtain ⟨AX,hAX,_,hXAX⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
  have hXS : X ≤ S := hXAX.trans hAX.1
  obtain ⟨AB,hAB,_,hBAB⟩ := h.automorphism_F_conjugate_submaximal S hB a.symm (hAll a.symm) t
  have hBS : B ≤ S := hBAB.trans hAB.1
  obtain ⟨AP,hAP,hAPQ,hPAP⟩ := h.inverse_conjugate_submaximal S hB a (hAll a) g hg (order_two_power g hg2)
  have hPQ : P ≤ pCore 2 H := hPAP.trans hAPQ
  obtain ⟨AT,hAT,_,hPtAT⟩ := h.submaximal_core_conjugate S hB P ⟨AP,hAP,hPAP⟩ hPQ t
  have hPtS : Pt ≤ S := hPtAT.trans hAT.1
  have hc := h.mixed_inverse_words_commute S hB a hAll hF g t hg ht hg2 ht2
  change ⁅X,Y⁆=⊥ at hc
  have hc1 := congrArg (automorphismImage S a.symm) hc
  rw [automorphismImage_commutator S a.symm X Y hXS (automorphismImage_le S a B),
    automorphismImage_bot S a.symm,automorphismImage_symm S a B hBS] at hc1
  have hc2 := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hc1
  rw [map_commutator,Subgroup.map_bot,conjugate_twice t ht2] at hc2
  have hc3 := congrArg (automorphismImage S a) hc2
  rw [automorphismImage_commutator S a Pt (automorphismImage S a.symm F) hPtS
    (automorphismImage_le S a.symm F),automorphismImage_bot S a] at hc3
  have hFid : automorphismImage S a (automorphismImage S a.symm F)=F := by
    simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm F hFS
  rw [hFid] at hc3
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  apply (h.sylow_centralizer_campbellF_le_core hB m d).trans'
  refine le_inf ?_ (commutator_eq_bot_iff_le_centralizer.mp hc3)
  rw [hSd]
  exact automorphismImage_le S a Pt
end CFSG.Quasithin.ChapterC.GlaubermanNiles
