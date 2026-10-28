module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Replacement
/-!
# The two elementary replacements in Campbell II.7

The actual automorphism image of F replaces a maximum elementary subgroup
inside the two-core. Its conjugate gives the second replacement. The fixed
layers bound the first commutator and force the required normalizer inclusion.
Source: Campbell, II.7.2(i), pp.33–34.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem aut_fixed_centralizes_sylow (a : MulAut S) :
    automorphismImage S a (fixed S) ≤ centralizer (S : Set H) := by
  rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩ t ht
  let ts : S := ⟨t,ht⟩
  have he : a.symm ts*z=z*a.symm ts := Subtype.ext (hz.2 _ (a.symm ts).property)
  have he' := congrArg a he
  have hh : ts*a z=a z*ts := by simpa only [map_mul,a.apply_symm_apply] using he'
  exact congrArg Subtype.val hh

theorem InLocalClass.firstReplacement_geometry (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    firstReplacement S a A ∈ elementaryAbelianMaxSubgroups S ∧
      firstReplacement S a A ≤ pCore 2 H ∧ Campbell.F H ≤ firstReplacement S a A ∧
      ⁅A,firstReplacement S a A⁆ ≤ fixed S ⊔ automorphismImage S a (fixed S) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  let Y := imageF S a
  let A0 := (A ⊓ pCore 2 H) ⊔ Campbell.F H
  let B0 := firstReplacement S a A
  let Z := fixed S
  let Za := automorphismImage S a Z
  have hA0 : A0 ∈ elementaryAbelianMaxSubgroups S := by
    rw [show A0=(A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) from
      h.campbellF_replacement_eq_omegaCore hB d A (hSd.symm ▸ hA)]
    simpa only [hSd] using h.omegaCore_replacement_maximal hB d A (hSd.symm ▸ hA)
  have hYQ : Y ≤ pCore 2 H := (le_conjugateSpanBy _ _).trans (h.sylow_automorphism_span S hB a hV).1
  have hYC : Y ≤ centralizer (Campbell.F H : Set H) := h.automorphism_F_centralizes_F S hB a hV
  have hB0 := h.automorphism_F_replacement S hB a A0 hA0
  have hB0Q : B0 ≤ pCore 2 H := sup_le hYQ (inf_le_left.trans (sup_le inf_le_right Campbell.F_le_pCore))
  have hFB0 : Campbell.F H ≤ B0 := (le_inf le_sup_right (le_centralizer_iff.mp hYC)).trans le_sup_right
  have hSN : S ≤ normalizer ((Z ⊔ Za : Subgroup H) : Set H) := by
    have hZC : Z ⊔ Za ≤ centralizer (S : Set H) := sup_le inf_le_right (aut_fixed_centralizes_sylow S a)
    exact (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  let D := commutatorPreimage S A (Z ⊔ Za)
  have hAD : A ≤ D := by
    apply le_commutatorPreimage hA.1
    let : IsElementaryAbelian 2 A := hA.2.1
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr inferInstance)]
    exact bot_le
  have hFD : Campbell.F H ≤ D := by
    apply le_commutatorPreimage (Campbell.F_le_pCore.trans hQS)
    rw [commutator_comm]
    exact (h.submaximal_commutator_F_le_fixed S hB A ⟨A,hA,le_rfl⟩).trans le_sup_left
  have hYD : Y ≤ D := by
    apply le_commutatorPreimage (hYQ.trans hQS)
    rw [commutator_comm]
    rcases h.automorphism_F_commutator_dichotomy S hB a A hA with hb | he
    · exact hb.le.trans bot_le
    · exact he.le.trans le_sup_right
  have hB0D : B0 ≤ D := sup_le hYD (inf_le_left.trans (sup_le (inf_le_left.trans hAD) hFD))
  refine ⟨hB0,hB0Q,hFB0,?_⟩
  rw [commutator_comm]
  exact (commutator_mono hB0D le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hSN)

theorem InLocalClass.replacement_geometry (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (g : H) :
    replacement S a A g ∈ elementaryAbelianMaxSubgroups S ∧
      replacement S a A g ≤ pCore 2 H ∧
      A ≤ normalizer (firstReplacement S a A ⊓ centralizer (inverseConjugate S a g : Set H) : Set H) := by
  let B0 := firstReplacement S a A
  let C := inverseConjugate S a g
  let Z := fixed S
  let Za := automorphismImage S a Z
  have hb := h.firstReplacement_geometry S hB a (hAll a) A hA
  have hc := h.automorphism_conjugate_replacement S hB a.symm (hAll a.symm) B0 hb.1 hb.2.1 g
  have hCQ : C ≤ pCore 2 H := by
    have hFQ := (le_conjugateSpanBy _ _).trans (h.sylow_automorphism_span S hB a.symm (hAll a.symm)).1
    rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem y (hFQ hy) g
  have hZB0 : Z ≤ B0 := (inf_le_left.trans Campbell.V_le_F).trans hb.2.2.1
  have hZaB0 : Za ≤ B0 := (automorphismImage_mono S a (inf_le_left.trans Campbell.V_le_F)).trans le_sup_left
  have hZZB0 : Z ⊔ Za ≤ B0 := sup_le hZB0 hZaB0
  have hZZS : Z ⊔ Za ≤ centralizer (S : Set H) := sup_le inf_le_right (aut_fixed_centralizes_sylow S a)
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hCS : C ≤ S := hCQ.trans (hST ▸ pCore_isPGroup.le_sylow_of_normal T)
  refine ⟨hc,sup_le hCQ (inf_le_left.trans hb.2.1),?_⟩
  change A ≤ normalizer ((B0 ⊓ centralizer (C : Set H) : Subgroup H) : Set H)
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl inf_le_left).trans (hb.2.2.2.trans
    (le_inf hZZB0 (hZZS.trans (centralizer_le hCS))))
end CFSG.Quasithin.ChapterC.GlaubermanNiles
