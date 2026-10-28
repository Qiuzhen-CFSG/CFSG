module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.WordControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.CommutatorValue

/-!
# Campbell II.7.3: the second replacement collapses

If the mixed actor lies in the second replacement, the commutator word
puts (B₀^g)^α in the two-core Thompson subgroup. Pulling back its
centralization of F shows B₀ centralizes F^(α⁻¹g). Maximum elementary
order then identifies the two original replacements. All subgroups are
the literal images from the source construction.
Source: Campbell, Pushing up in Finite Groups, II.7.3, pp.34–35.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.replacement_eq_first_of_mixed_le
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H)
    (hg2 : g^2=1) (hgM : g ∉ M)
    (hy : mixedActor S a g ≤ replacement S a A g) :
    replacement S a A g = firstReplacement S a A := by
  let P := firstReplacement S a A
  let C := inverseConjugate S a g
  let R := Campbell.J (pCore 2 H)
  let Z := fixed S
  have hp := h.firstReplacement_geometry S hB a (hAll a) A hA
  have hb := h.replacement_geometry S hB a hAll A hA g
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hR : R ≤ pCore 2 H := sSup_le fun _ hX => hX.1
  have hPR : P ≤ R := le_sSup
    ⟨hp.2.1,hp.1.2.1,fun D hd hde => hp.1.2.2 D (hd.trans hQS) hde⟩
  have hPg : P.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro x ⟨y,hy,rfl⟩
    exact hQS ((inferInstance : (pCore 2 H).Normal).conj_mem y (hp.2.1 hy) g)
  have hFg : (imageF S a).map (MulAut.conj g).toMonoidHom ≤ S := by
    obtain ⟨D,hd,_,hfd⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
    exact hfd.trans hd.1
  have hZS : Z ≤ S := (inf_le_left.trans Campbell.V_le_pCore).trans hQS
  let : IsElementaryAbelian 2 P := hp.1.2.1
  have hPB : ⁅P,replacement S a A g⁆=⁅P,C⁆ := by
    apply commutator_eq_of_product_centralizing_factor
      (coe_mul_of_left_le_normalizer_right C (P ⊓ centralizer (C : Set H))
        ((le_centralizer_iff.mp (show P ⊓ centralizer (C : Set H) ≤ centralizer (C : Set H) from inf_le_right)).trans
          (Subgroup.centralizer_le_normalizer _)))
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show P ⊓ centralizer (C : Set H) ≤ P from inf_le_left))
  have hr0 := h.automorphism_conjugate_core_commutator S hB a.symm (hAll a.symm) 1 (one_mem _)
  have he1 : (MulAut.conj (1:H)).toMonoidHom=MonoidHom.id H := by ext x;simp
  rw [he1,Subgroup.map_id,commutator_comm] at hr0
  let : R.Normal := Campbell.core_thompson_normal
  have hRg : R.map (MulAut.conj g).toMonoidHom=R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hrg := map_mono (f := (MulAut.conj g).toMonoidHom) hr0
  change (⁅R,imageF S a.symm⁆).map (MulAut.conj g).toMonoidHom ≤
    (automorphismImage S a.symm Z).map (MulAut.conj g).toMonoidHom at hrg
  rw [map_commutator,hRg] at hrg
  have hc : ⁅P,mixedActor S a g⁆ ≤
      (automorphismImage S a.symm Z).map (MulAut.conj g).toMonoidHom :=
    (commutator_mono le_rfl hy).trans (hPB.le.trans ((commutator_mono hPR le_rfl).trans hrg))
  have hdc := mixed_commutator_bound_transport S a g hg2 P Z hPg hFg hZS hc
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hZgF : Z.map (MulAut.conj g).toMonoidHom ≤ Campbell.F H := by
    rintro x ⟨z,hz,rfl⟩
    exact (inferInstance : (Campbell.F H).Normal).conj_mem z (Campbell.V_le_F hz.1) g
  have hDR := h.double_conjugate_maximum_le_core_thompson S hB M hM g hgM a P hp.1 hp.2.1
    (imageF S a) ((h.automorphism_thompson_commutator_le_fixed S hB a).trans
      (h.automorphism_fixed_le_F S hB a (hAll a))) hn (hdc.trans hZgF)
  have hDF : ⁅automorphismImage S a (P.map (MulAut.conj g).toMonoidHom),Campbell.F H⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply hDR.trans
    apply le_centralizer_iff.mp
    exact fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2
  have hback := congrArg (automorphismImage S a.symm) hDF
  rw [automorphismImage_commutator S a.symm _ _ (automorphismImage_le S a _) (Campbell.F_le_pCore.trans hQS),
    automorphismImage_symm S a _ hPg,automorphismImage_bot] at hback
  have hzero := congrArg (fun X : Subgroup H => X.map (MulAut.conj g).toMonoidHom) hback
  rw [map_commutator,conj_twice g hg2,Subgroup.map_bot] at hzero
  have hPC : P ≤ centralizer (C : Set H) := commutator_eq_bot_iff_le_centralizer.mp hzero
  have hPle : P ≤ replacement S a A g := (le_inf le_rfl hPC).trans le_sup_right
  exact (Subgroup.eq_of_le_of_card_ge hPle (hp.1.2.2 _ hb.1.1 hb.1.2.1)).symm

/-- Campbell II.7.4 for the original inverse automorphism and ambient Thompson group. -/
theorem InLocalClass.inverse_global_commutator_le_of_mixed_le
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : ¬A ≤ pCore 2 H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H)
    (hg2 : g^2=1) (hgM : g ∉ M)
    (hy : mixedActor S a g ≤ replacement S a A g) :
    ⁅Campbell.J (⊤ : Subgroup H),imageF S a.symm⁆ ≤ Campbell.F H := by
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hp := h.firstReplacement_geometry S hB a (hAll a) A hA
  have he := h.replacement_eq_first_of_mixed_le S hB a hAll hn A hA M hM g hg2 hgM hy
  have hc : inverseConjugate S a g ≤ firstReplacement S a A :=
    (show inverseConjugate S a g ≤ replacement S a A g from le_sup_left).trans he.le
  have hZF : fixed S ⊔ automorphismImage S a (fixed S) ≤ Campbell.F H :=
    sup_le (inf_le_left.trans Campbell.V_le_F) (h.automorphism_fixed_le_F S hB a (hAll a))
  have hAg := map_mono (f := (MulAut.conj g).toMonoidHom)
    ((commutator_mono le_rfl hc).trans (hp.2.2.2.trans hZF))
  change (⁅A,(imageF S a.symm).map (MulAut.conj g).toMonoidHom⁆).map
    (MulAut.conj g).toMonoidHom ≤ _ at hAg
  have hFg : (Campbell.F H).map (MulAut.conj g).toMonoidHom=Campbell.F H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [map_commutator,conj_twice g hg2,hFg] at hAg
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn',k,_,_,_,hk,⟨m⟩⟩ := h.natural
  let N := commutatorPreimage (⊤ : Subgroup H) (imageF S a.symm) (Campbell.F H)
  have hT : Campbell.J S ≤ N := le_commutatorPreimage le_top
    ((h.automorphism_thompson_commutator_le_fixed S hB a.symm).trans
      (h.automorphism_fixed_le_F S hB a.symm (hAll a.symm)))
  have hN := h.global_thompson_le_of_two_maxima hB m d hS A (hs.symm ▸ hA) hAQ M
    (by rwa [hs]) g hgM N (by rwa [hs]) (le_commutatorPreimage le_top hAg)
  exact (commutator_mono hN le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
