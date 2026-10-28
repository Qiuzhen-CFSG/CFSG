module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Collapse
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.CommonFamily

/-!
# Campbell II.7.5: noncontainment of the mixed actor

The second replacement cannot contain the mixed actor. Otherwise II.7.3
identifies it with the first replacement. Both X=J(C_Q(FF^(α⁻¹))) and
FF^(αgα⁻¹) are then normalized by A^g. Their commutator is Z, as follows
by transporting [X^α,F^(αg)]=Z^α. Thus A^g normalizes Z, contradicting
the source maximal-subgroup separation. Every map is literal.
Source: Campbell, Pushing up in Finite Groups, II.7.5, printed p.35.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.mixedActor_not_le_replacement
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : ¬A ≤ pCore 2 H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤)
    (hNZ : normalizer (fixed S : Set H) ≤ M) (g : H)
    (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) (hg2 : g^2=1) (hgM : g ∉ M) :
    ¬ mixedActor S a g ≤ replacement S a A g := by
  intro hy
  let P := firstReplacement S a A
  let X := commonThompson S a
  let W := automorphismImage S a.symm ((imageF S a).map (MulAut.conj g).toMonoidHom)
  let Ag := A.map (MulAut.conj g).toMonoidHom
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hFg : (Campbell.F H).map (MulAut.conj g).toMonoidHom=Campbell.F H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans hQS
  have hZS : fixed S ≤ S := (inf_le_left.trans Campbell.V_le_pCore).trans hQS
  have hp := h.firstReplacement_geometry S hB a (hAll a) A hA
  have hcollapse := h.replacement_eq_first_of_mixed_le S hB a hAll hn A hA M hM g hg2 hgM hy
  have hCP : inverseConjugate S a g ≤ P := (show inverseConjugate S a g ≤
    replacement S a A g from le_sup_left).trans hcollapse.le
  have hyP : mixedActor S a g ≤ P := hy.trans hcollapse.le
  have hZF : fixed S ⊔ automorphismImage S a (fixed S) ≤ Campbell.F H :=
    sup_le (inf_le_left.trans Campbell.V_le_F) (h.automorphism_fixed_le_F S hB a (hAll a))
  have hAP : ⁅A,P⁆ ≤ Campbell.F H := hp.2.2.2.trans hZF
  have hAgF : ⁅Ag,imageF S a.symm⁆ ≤ Campbell.F H := by
    have hc := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((commutator_mono le_rfl hCP).trans hAP)
    change (⁅A,(imageF S a.symm).map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom ≤ _ at hc
    rwa [map_commutator,conj_twice g hg2,hFg] at hc
  have hAgW : ⁅Ag,W⁆ ≤ Campbell.F H := by
    have hc := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((commutator_mono le_rfl hyP).trans hAP)
    change (⁅A,W.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom ≤ _ at hc
    rwa [map_commutator,conj_twice g hg2,hFg] at hc
  have hAgNFi : Ag ≤ normalizer ((Campbell.F H ⊔ imageF S a.symm : Subgroup H) : Set H) := by
    have he := le_normalizer_sup_of_commutator_le (imageF S a.symm) Ag
      (imageF S a.symm) (Campbell.F H) le_rfl ((commutator_comm _ _).le.trans hAgF)
    simpa only [sup_comm] using he
  have hAgNW : Ag ≤ normalizer ((Campbell.F H ⊔ W : Subgroup H) : Set H) := by
    have he := le_normalizer_sup_of_commutator_le W Ag W (Campbell.F H) le_rfl
      ((commutator_comm _ _).le.trans hAgW)
    simpa only [sup_comm] using he
  have hx := common_thompson_bounds_of_contains_imageF S h hB a P hp.1 hp.2.1
    (show imageF S a ≤ P from le_sup_left)
  have hXR : X ≤ Campbell.J (pCore 2 H) := hx.2.1
  have hXS : X ≤ S := (hXR.trans (sSup_le fun _ hb => hb.1)).trans hQS
  have hXaR : automorphismImage S a X ≤ Campbell.J (pCore 2 H) := hx.2.2
  have hPXa : P ≤ automorphismImage S a X := by
    have he := automorphismImage_mono S a hx.1
    have hc := automorphismImage_symm S a.symm P hp.1.1
    simp only [MulEquiv.symm_symm] at hc
    rwa [hc] at he
  have hFagS : (imageF S a).map (MulAut.conj g).toMonoidHom ≤ S := by
    obtain ⟨D,hd,_,hf⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
    exact hf.trans hd.1
  have haW : automorphismImage S a W=(imageF S a).map (MulAut.conj g).toMonoidHom := by
    simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm _ hFagS
  have hcomm : ⁅automorphismImage S a X,(imageF S a).map (MulAut.conj g).toMonoidHom⁆ =
      automorphismImage S a (fixed S) := by
    apply le_antisymm
    · exact (commutator_mono hXaR le_rfl).trans
        (h.core_conjugate_commutator_value S hB a (hAll a) hn A hA hAQ M hM g hgK hg2 hgM).le
    · exact (h.firstReplacement_commutator_value S hB a (hAll a) hn A hA hAQ M hM g hg2 hgM).symm.le.trans
        (commutator_mono hPXa le_rfl)
  have hXW : ⁅X,W⁆=fixed S := by
    have ht : automorphismImage S a ⁅X,W⁆=automorphismImage S a (fixed S) := by
      rw [automorphismImage_commutator S a X W hXS (automorphismImage_le S a.symm _),haW]
      exact hcomm
    have hb := congrArg (automorphismImage S a.symm) ht
    rwa [automorphismImage_symm S a _ ((_root_.commutator_le_sup _ _).trans
      (sup_le hXS (automorphismImage_le S a.symm _))),automorphismImage_symm S a _ hZS] at hb
  have hXFC : X ≤ centralizer (Campbell.F H : Set H) := by
    apply hXR.trans
    apply le_centralizer_iff.mp
    exact fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2
  have hXP : ⁅X,Campbell.F H ⊔ W⁆=fixed S := by
    calc
      ⁅X,Campbell.F H ⊔ W⁆=⁅X,W⁆ := by
        apply commutator_eq_of_product_centralizing_factor
          (by rw [sup_comm]; exact coe_mul_of_left_le_normalizer_right W (Campbell.F H) le_normalizer_of_normal)
        exact hXFC
      _=fixed S := hXW
  have hAgX : Ag ≤ normalizer (X : Set H) := common_thompson_normalized S a Ag hAgNFi
  have hAgZ : Ag ≤ normalizer (fixed S : Set H) := by
    rw [←hXP]
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxX : X.map (MulAut.conj x).toMonoidHom=X := mem_normalizer_iff_map_conj_eq.mp (hAgX hx)
    have hxW : (Campbell.F H ⊔ W).map (MulAut.conj x).toMonoidHom=Campbell.F H ⊔ W :=
      mem_normalizer_iff_map_conj_eq.mp (hAgNW hx)
    change (⁅X,Campbell.F H ⊔ W⁆).map (MulAut.conj x).toMonoidHom = _
    rw [map_commutator,hxX,hxW]
  obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hAQ
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn',k,_,_,_,hk,⟨m⟩⟩ := h.natural
  exact h.campbell_maximal_separation hB m d hS M (by rwa [hs]) g x hgM
    (by change x∈(d.sylow:Subgroup H);rw [hs];exact hA.1 hx) hxQ
    (hNZ (hAgZ (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)))
end CFSG.Quasithin.ChapterC.GlaubermanNiles
