module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.OrbitContainment
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Stellmacher.ElementaryAbelianMaxGlobal


/-!
# Campbell's two-overgroup comparison from the original local hypotheses

The orbit containment gives normalization of FF′ by a conjugate moving
maximum elementary subgroup. Together with J(S), that conjugate generates
a supplement to O₂(H), hence contains J(H). Thus J(H) normalizes FF′.
If F′ is not contained in F, a maximum elementary subgroup of O₂(H)
does not centralize F′. The paired commutator dichotomy gives
[J(O₂(H)),F′]=Z′. Since F centralizes J(O₂(H)), normalization of FF′
makes Z′ J(H)-invariant. The original supplement geometry then forces
Z′ to centralize J(H), completing the comparison.

The final theorem proves the literal `Campbell.ComparisonConclusion`
with both original embeddings, quotient conventions and ambient Sylow
markings. It assumes no factorization or comparison output.
Source: Campbell, *Pushing up in Finite Groups* (1979), Theorem B,
II.5.5 and its conclusion, printed pp.28–29; Aschbacher–Smith C.1.17–18.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

omit [Finite H] in
private theorem core_normalizes_thompson (d : Campbell.Embedding J H) :
    pCore 2 H ≤ normalizer (Campbell.J (d.sylow : Subgroup H) : Set H) := by
  intro q hq
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ (d.sylow : Subgroup H)).map (MulAut.conj q).toMonoidHom = _
  rw [←elementaryAbelianMaxJ_map_equiv]
  have hs := mem_normalizer_iff_map_conj_eq.mp ((d.sylow : Subgroup H).le_normalizer
    (pCore_isPGroup.le_sylow_of_normal d.sylow hq))
  change (d.sylow : Subgroup H).map (MulAut.conj q).toMonoidHom = (d.sylow : Subgroup H) at hs
  rw [hs]
  rfl

omit [Finite H] in
private theorem closure_le_of_supplement (T Q N : Subgroup H) [Q.Normal]
    (hQT : Q ≤ normalizer (T : Set H)) (hTN : T ≤ N) (hgen : N ⊔ Q = ⊤) :
    normalClosure (T : Set H) ≤ N := by
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨t,ht,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g,rfl⟩ := isConj_iff.mp hconj
  obtain ⟨n,hn,q,hq,rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top g)
  have htq := (mem_normalizer_iff.mp (hQT hq) t).mp ht
  have hh := N.mul_mem (N.mul_mem hn (hTN htq)) (N.inv_mem hn)
  change (n*q)*t*(n*q)⁻¹ ∈ N
  simpa only [mul_inv_rev,mul_assoc] using hh

theorem InLocalClass.global_thompson_le_of_two_maxima (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : ¬ A ≤ pCore 2 H) (M : Subgroup H)
    (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤) (g : H) (hg : g ∉ M)
    (N : Subgroup H) (hTN : Campbell.J (d.sylow : Subgroup H) ≤ N)
    (hAgN : A.map (MulAut.conj g).toMonoidHom ≤ N) :
    Campbell.J (⊤ : Subgroup H) ≤ N := by
  obtain ⟨S0,he,hS0⟩ := h.sylow
  have hu : Order.HasUniqueMaximalOver (d.sylow : Subgroup H) ⊤ := by
    rw [hS,he]; exact hS0.1
  have hgen : N ⊔ pCore 2 H = ⊤ := by
    by_contra hn
    have hSle : (d.sylow : Subgroup H) ≤ N ⊔ pCore 2 H := by
      rw [←h.thompson_sup_core_eq_sylow hB m d hS]
      exact sup_le_sup hTN le_rfl
    have hNM := hu.le_maximal hM hSle (lt_top_iff_ne_top.mpr hn)
    obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hAQ
    exact h.campbell_maximal_separation hB m d hS M hM g x hg (hA.1 hx) hxQ
      (hNM ((show N ≤ N ⊔ pCore 2 H from le_sup_left)
        (hAgN (mem_map_of_mem (MulAut.conj g).toMonoidHom hx))))
  change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ N
  rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow d.sylow]
  exact closure_le_of_supplement _ _ _ (core_normalizes_thompson d) hTN hgen

theorem InLocalClass.paired_join_normalized (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hn : ¬ d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤
      centralizer (Campbell.J (⊤ : Subgroup H) : Set H)) :
    Campbell.J (⊤ : Subgroup H) ≤ normalizer
      ((Campbell.F H ⊔ d.transfer d' (Campbell.F H') : Subgroup H) : Set H) := by
  obtain ⟨M,hSM,hMt,hNZ,hbound⟩ := h.exists_paired_orbit_containment hB m h' hB' m' d d' hS hS' hV hn
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ¬ A ≤ pCore 2 H := by
    by_contra! hall
    have hJQ : elementaryAbelianMaxJ (d.sylow : Subgroup H) ≤ pCore 2 H := sSup_le hall
    apply h.thompson_moves_moved hB d.sylow hS.symm
    exact hJQ.trans (le_centralizer_iff.mp (h.moved_le_coreOmegaCenter.trans
      (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2)))
  obtain ⟨A,hA,hAQ⟩ := hex
  obtain ⟨g,_,hg⟩ := Set.not_subset.mp (show ¬ (⊤ : Subgroup H) ≤ M from fun hh => hMt.ne (top_unique hh))
  let Y := d.transfer d' (Campbell.F H')
  let P := Campbell.F H ⊔ Y
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hTP : Campbell.J (d.sylow : Subgroup H) ≤ normalizer (P : Set H) :=
    (le_inf le_normalizer_of_normal (h.paired_core_geometry hB m h' hB' m' d d' hV).2.2.1).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hAYg : ⁅A,Y.map (MulAut.conj g).toMonoidHom⁆ ≤ Campbell.F H :=
    (commutator_mono le_rfl (hbound A hA hAQ g hg)).trans
      (h.paired_replacement_geometry hB m h' hB' m' d d' hS' hV A hA).2.2.2.2.1
  have hAgY : ⁅A.map (MulAut.conj g⁻¹).toMonoidHom,Y⁆ ≤ Campbell.F H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAYg
    rw [map_commutator] at hh
    have hy : (Y.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = Y := by
      rw [Subgroup.map_map]
      have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id H := by
        ext y; simp [MulAut.conj_apply,mul_assoc]
      rw [he,Subgroup.map_id]
    have hf : (Campbell.F H).map (MulAut.conj g⁻¹).toMonoidHom = Campbell.F H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
    rwa [hy,hf] at hh
  have hAgP : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (P : Set H) := by
    have hh := le_normalizer_sup_of_commutator_le Y (A.map (MulAut.conj g⁻¹).toMonoidHom) Y (Campbell.F H)
      le_rfl ((commutator_comm _ _).le.trans hAgY)
    simpa only [sup_comm] using hh
  exact InLocalClass.global_thompson_le_of_two_maxima h hB m d hS A hA hAQ M ⟨hSM,hMt⟩ g⁻¹
    (fun hi => hg (by simpa using M.inv_mem hi)) _ hTP hAgP

theorem InLocalClass.paired_core_commutator (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hF : ¬ d.transfer d' (Campbell.F H') ≤ Campbell.F H) :
    ⁅Campbell.J (pCore 2 H),d.transfer d' (Campbell.F H')⁆ =
      d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) := by
  let R := Campbell.J (pCore 2 H)
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  have hYQ := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  obtain ⟨A,hA,hYA⟩ := h'.campbellF_le_some_maxElementary hB' d'
  have hYA' : Y ≤ d.transfer d' A := map_mono (comap_mono hYA)
  let : IsElementaryAbelian 2 (d.transfer d' A) := (d.transfer_maxElementary d' A hA).2.1
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYA'
  have hYR : Y ≤ R := h.submaximal_core_le_thompson hB d _ _
    (d.transfer_maxElementary d' A hA) hYA' hYQ
  have hRJ : R ≤ Campbell.J (d.sylow : Subgroup H) := sSup_le fun A hA =>
    le_sSup (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hA)
  have hRZ : R ≤ centralizer (Z : Set H) :=
    hRJ.trans (le_centralizer_iff.mp (d.transferred_fixed_centralizes_thompson d'))
  have hDZ : ∀ X ∈ elementaryAbelianMaxSubgroups (pCore 2 H), ⁅X,Y⁆ ≤ Z := by
    intro X hX
    rcases h'.paired_campbellF_commutator_dichotomy hB' m' d d' hS' X
      (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hX) with hb | hz
    · exact hb.le.trans bot_le
    · exact hz.le
  have hle : ⁅R,Y⁆ ≤ Z := by
    have hRP : R ≤ commutatorPreimage R Y Z := sSup_le fun X hX =>
      le_commutatorPreimage (le_sSup hX) (hDZ X hX)
    exact (commutator_mono hRP le_rfl).trans (commutator_commutatorPreimage_le R Y Z
      (hRZ.trans (Subgroup.centralizer_le_normalizer _)))
  have hex : ∃ X ∈ elementaryAbelianMaxSubgroups (pCore 2 H), ⁅X,Y⁆ ≠ ⊥ := by
    by_contra! hall
    have hRC : R ≤ centralizer (Y : Set H) := sSup_le fun X hX =>
      commutator_eq_bot_iff_le_centralizer.mp (hall X hX)
    apply hF
    intro y hy
    exact (mem_omegaOneCenterAmbient_iff R y).mpr ⟨hYR hy,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy,(le_centralizer_iff.mp hRC) hy⟩
  obtain ⟨X,hX,hne⟩ := hex
  rcases h'.paired_campbellF_commutator_dichotomy hB' m' d d' hS' X
    (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hX) with hb | hz
  · exact False.elim (hne hb)
  · exact le_antisymm hle (hz.symm.le.trans (commutator_mono (le_sSup hX) le_rfl))

theorem InLocalClass.paired_comparison_centrality (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hF : ¬ d.transfer d' (Campbell.F H') ≤ Campbell.F H) :
    d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤
      centralizer (Campbell.J (⊤ : Subgroup H) : Set H) := by
  by_contra hn
  let R := Campbell.J (pCore 2 H)
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  let P := Campbell.F H ⊔ Y
  have hnP := InLocalClass.paired_join_normalized h hB m h' hB' m' d d' hS hS' hV hn
  let : R.Normal := Campbell.core_thompson_normal
  have hRZ : ⁅R,Y⁆ = Z := InLocalClass.paired_core_commutator h hB m h' hB' m' d d' hS' hV hF
  have hFR : Campbell.F H ≤ centralizer (R : Set H) :=
    fun f hf => ((mem_omegaOneCenterAmbient_iff R f).mp hf).2.2
  have hRP : ⁅R,P⁆ = Z := (commutator_eq_of_centralizing_sup rfl hFR le_normalizer_of_normal).symm.trans hRZ
  have hJZ : Campbell.J (⊤ : Subgroup H) ≤ normalizer (Z : Set H) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←hRP,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (R : Set H) from le_normalizer_of_normal (mem_top g)),
      mem_normalizer_iff_map_conj_eq.mp (hnP hg)]
  have hTJ : Campbell.J (d.sylow : Subgroup H) ≤ Campbell.J (⊤ : Subgroup H) :=
    elementaryAbelianMaxJ_sylow_le_top d.sylow
  have hNZ : Campbell.J (⊤ : Subgroup H) ≤ normalizer (Z : Set H) := hJZ
  have hTJn : (Campbell.J (⊤ : Subgroup H)).Normal := by
    change (elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal
    let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic := elementaryAbelianMaxJ_top_characteristic
    infer_instance
  have hglobal : normalClosure (Campbell.J (d.sylow : Subgroup H) : Set H) ≤ centralizer (Z : Set H) :=
    closure_centralizes_of_normalizer_supplement _ _ Z (core_normalizes_thompson d)
      (le_centralizer_iff.mp (d.transferred_fixed_centralizes_thompson d')) (by
        apply top_unique
        obtain ⟨g,_,hgen⟩ := h.exists_two_sylow_generators hB m d hS
        have hJQ : Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H = ⊤ := by
          have hNg : (Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H).Normal := inferInstance
          have hSN : (d.sylow : Subgroup H) ≤ Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
            rw [←h.thompson_sup_core_eq_sylow hB m d hS]
            exact sup_le_sup hTJ le_rfl
          have hSgN : (d.sylow : Subgroup H).map (MulAut.conj g).toMonoidHom ≤
              Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
            intro x hx
            obtain ⟨s,hs,rfl⟩ := hx
            exact hNg.conj_mem s (hSN hs) g
          exact top_unique (hgen.symm.le.trans (sup_le hSN hSgN))
        rw [←hJQ]
        exact sup_le_sup hNZ le_rfl)
  apply hn
  apply le_centralizer_iff.mpr
  change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ centralizer (Z : Set H)
  rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow d.sylow]
  exact hglobal


theorem InLocalClass.campbell_comparison (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range) :
    Campbell.ComparisonConclusion d d' := by
  intro hV hF
  have hc := InLocalClass.paired_comparison_centrality h hB m h' hB' m' d d' hS hS' hV hF
  have hs : ⁅(d'.sylow : Subgroup H'),Campbell.V H'⁆ =
      Campbell.V H' ⊓ centralizer (d'.sylow : Set H') := by
    rw [h'.campbellV_eq_moved hB' m']
    exact (h'.sylow_fixed_eq_commutator hB' m' d' hS').symm
  rw [hs]
  intro z hz
  have hzJ : z ∈ Campbell.J (⊤ : Subgroup H) := by
    apply elementaryAbelianMaxJ_sylow_le_top d.sylow
    change z ∈ Campbell.J (d.sylow : Subgroup H)
    rw [←d.range_eq]
    exact map_le_range _ _ hz
  refine ⟨⟨z,hzJ⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact (hc hz) g g.property

end CFSG.Quasithin.ChapterC.GlaubermanNiles
