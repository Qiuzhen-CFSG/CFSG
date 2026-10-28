module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.FirstReplacement
/-!
# The nonzero replacement commutator

The maximum elementary alternatives sum to a Thompson bound. If the
conjugate of F lies in the first replacement, two maximum subgroups
generate the ambient Thompson group and contradict the chosen failure
of Theorem A. Thus the replacement and core commutators equal the
transported fixed layer. Source: Campbell II.7.2(iii), pp.33–34.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem fixed_central (a : MulAut S) :
    automorphismImage S a (fixed S) ≤ centralizer (S : Set H) := by
  rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩ t ht
  let ts : S := ⟨t,ht⟩
  have he : a.symm ts*z=z*a.symm ts := Subtype.ext (hz.2 _ (a.symm ts).property)
  have he' := congrArg a he
  have hh : ts*a z=a z*ts := by simpa only [map_mul,a.apply_symm_apply] using he'
  exact congrArg Subtype.val hh

theorem InLocalClass.automorphism_thompson_commutator_le_fixed
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S) :
    ⁅Campbell.J S,imageF S a⁆ ≤ automorphismImage S a (fixed S) := by
  let Z := automorphismImage S a (fixed S)
  let D := commutatorPreimage S (imageF S a) Z
  have hJD : Campbell.J S ≤ D := by
    apply sSup_le
    intro A hA
    apply le_commutatorPreimage hA.1
    rcases h.automorphism_F_commutator_dichotomy S hB a A hA with hh | hh
    · exact hh.le.trans bot_le
    · exact hh.le
  have hSN : S ≤ normalizer (Z : Set H) :=
    (le_centralizer_iff.mp (fixed_central S a)).trans (Subgroup.centralizer_le_normalizer _)
  exact (commutator_mono hJD le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hSN)

theorem InLocalClass.automorphism_fixed_le_F
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    automorphismImage S a (fixed S) ≤ Campbell.F H := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨A,hA,hYA⟩ := h.automorphism_F_submaximal S hB a
  have hYQ := (le_conjugateSpanBy _ _).trans (h.sylow_automorphism_span S hB a hV).1
  have hYR := h.submaximal_core_le_thompson hB d _ A (hSd.symm ▸ hA) hYA hYQ
  have hZY := automorphismImage_mono S a (show fixed S ≤ Campbell.F H from inf_le_left.trans Campbell.V_le_F)
  have hRS : Campbell.J (pCore 2 H) ≤ S :=
    (sSup_le fun _ hA => hA.1).trans (hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow)
  let : IsElementaryAbelian 2 A := hA.2.1
  intro z hz
  exact (mem_omegaOneCenterAmbient_iff _ z).mpr ⟨hYR (hZY hz),
    elemPow_eq_one_of_isElementaryAbelian (p:=2) z (hYA (hZY hz)),
    fun q hq => fixed_central S a hz q (hRS hq)⟩

omit [Finite H] in
private theorem conj_twice (g : H) (hg : g^2=1) (X : Subgroup H) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom=X := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id H := by
    ext x
    have hgg : g*g=1 := by simpa only [pow_two] using hg
    have hgi : g⁻¹=g := inv_eq_of_mul_eq_one_left hgg
    change g*(g*x*g⁻¹)*g⁻¹=x
    rw [hgi]
    calc
      g*(g*x*g)*g = (g*g)*x*(g*g) := by group
      _=x := by rw [hgg,one_mul,mul_one]
  rw [he,Subgroup.map_id]

theorem InLocalClass.firstReplacement_commutator_value
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : ¬A ≤ pCore 2 H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H)
    (hg2 : g^2=1) (hgM : g ∉ M) :
    ⁅firstReplacement S a A,(imageF S a).map (MulAut.conj g).toMonoidHom⁆ =
      automorphismImage S a (fixed S) := by
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hF : ¬imageF S a ≤ Campbell.F H := fun hf => hn ((commutator_mono le_rfl hf).trans (commutator_le_right _ _))
  have hZC := h.automorphism_fixed_le_center S hB a hV hF
  have hZg : (automorphismImage S a (fixed S)).map (MulAut.conj g).toMonoidHom =
      automorphismImage S a (fixed S) := by
    apply le_antisymm
    · rintro x ⟨z,hz,rfl⟩
      have hc := (mem_center_iff.mp (hZC hz)) g
      change g*z*g⁻¹ ∈ automorphismImage S a (fixed S)
      rw [hc,mul_inv_cancel_right]
      exact hz
    · intro z hz
      refine ⟨z,hz,?_⟩
      have hc := (mem_center_iff.mp (hZC hz)) g
      change g*z*g⁻¹=z
      rw [hc,mul_inv_cancel_right]
  have hb := h.firstReplacement_geometry S hB a hV A hA
  have hYnot : ¬(imageF S a).map (MulAut.conj g).toMonoidHom ≤ firstReplacement S a A := by
    intro hy
    have hcomm := (commutator_mono le_rfl hy).trans hb.2.2.2
    have hZF : fixed S ⊔ automorphismImage S a (fixed S) ≤ Campbell.F H :=
      sup_le (inf_le_left.trans Campbell.V_le_F) (h.automorphism_fixed_le_F S hB a hV)
    have hc := map_mono (f:=(MulAut.conj g).toMonoidHom) (hcomm.trans hZF)
    rw [map_commutator,conj_twice g hg2] at hc
    have hFg : (Campbell.F H).map (MulAut.conj g).toMonoidHom=Campbell.F H :=
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (Campbell.F H : Set H) from le_normalizer_of_normal (mem_top g))
    rw [hFg] at hc
    let D := commutatorPreimage (⊤ : Subgroup H) (imageF S a) (Campbell.F H)
    have hTD : Campbell.J S ≤ D := le_commutatorPreimage le_top
      ((h.automorphism_thompson_commutator_le_fixed S hB a).trans (h.automorphism_fixed_le_F S hB a hV))
    have hAgD : A.map (MulAut.conj g).toMonoidHom ≤ D := le_commutatorPreimage le_top hc
    obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
    have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
    obtain ⟨n,hprime,k,_,_,_,hk,⟨m⟩⟩ := h.natural
    have hKD := h.global_thompson_le_of_two_maxima hB m d hS A (hSd.symm ▸ hA) hAQ M
      (by rwa [hSd]) g hgM D (by rwa [hSd]) hAgD
    exact hn ((commutator_mono hKD le_rfl).trans (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal))
  rcases h.automorphism_conjugate_commutator_dichotomy S hB a _ hb.1 hb.2.1 g with hz | he
  · exfalso
    apply hYnot
    obtain ⟨C,hC,_,hYC⟩ := h.automorphism_F_conjugate_submaximal S hB a hV g
    let : IsElementaryAbelian 2 C := hC.2.1
    let : IsElementaryAbelian 2 ((imageF S a).map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.of_le hYC
    exact maxElementary_contains_elementary_centralizer S _ _ hb.1 (hYC.trans hC.1)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  · exact he.trans hZg

theorem InLocalClass.core_conjugate_commutator_value
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : ¬A ≤ pCore 2 H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H)
    (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) (hg2 : g^2=1) (hgM : g ∉ M) :
    ⁅Campbell.J (pCore 2 H),(imageF S a).map (MulAut.conj g).toMonoidHom⁆ =
      automorphismImage S a (fixed S) := by
  have hb := h.firstReplacement_geometry S hB a hV A hA
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hBR := h.submaximal_core_le_thompson hB d _ _ (hSd.symm ▸ hb.1) le_rfl hb.2.1
  apply le_antisymm
  · rw [commutator_comm]
    exact h.automorphism_conjugate_core_commutator S hB a hV g hgK
  · exact (h.firstReplacement_commutator_value S hB a hV hn A hA hAQ M hM g hg2 hgM).symm.le.trans
      (commutator_mono hBR le_rfl)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
