module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Definitions
public import Theory.GroupTheory.SubgroupAutomorphismImages.Operations
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The common maximum family in Campbell II.7.5

For a maximum elementary subgroup A in the two-core which contains F^α,
its inverse image A^(α⁻¹) is a maximum subgroup of C_Q(FF^(α⁻¹)).
The Thompson subgroup X of that literal centralizer contains A^(α⁻¹),
and both X and X^α lie in J(Q). The point-centralizer theorem supplies
the second core bound. Normalizing FF^(α⁻¹) therefore normalizes X.
Source: Campbell, Pushing up in Finite Groups, II.7.5, printed p.35.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

private theorem core_point_centralizer (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) :
    S ⊓ centralizer (Campbell.F H : Set H) ≤ pCore 2 H := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  rw [←hs]
  exact h.sylow_centralizer_campbellF_le_core hB m d

namespace CampbellTheoremA
@[expose] noncomputable def commonCore (a : MulAut S) : Subgroup H :=
  pCore 2 H ⊓ centralizer ((Campbell.F H ⊔ imageF S a.symm : Subgroup H) : Set H)
@[expose] noncomputable def commonThompson (a : MulAut S) : Subgroup H := Campbell.J (commonCore S a)

omit [Finite H] in
private theorem core_thompson_centralizes_F :
    Campbell.J (pCore 2 H) ≤ centralizer (Campbell.F H : Set H) := by
  apply le_centralizer_iff.mp
  exact fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2

variable (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
  (a : MulAut S) (A : Subgroup H)
  (hA : A ∈ elementaryAbelianMaxSubgroups S)
  (hAR : A ≤ Campbell.J (pCore 2 H))
  (hAaR : automorphismImage S a.symm A ≤ Campbell.J (pCore 2 H))

include h hA hAR hAaR in
 theorem common_maximum : automorphismImage S a.symm A ∈ elementaryAbelianMaxSubgroups (commonCore S a) := by
  have hAS := automorphismImage_maxElementary S a.symm A hA
  refine ⟨?_,hAS.2.1,fun B hB hBe => hAS.2.2 B ?_ hBe⟩
  · refine le_inf (hAaR.trans (sSup_le fun _ hX => hX.1)) ?_
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (hAaR.trans core_thompson_centralizes_F))
      (le_centralizer_iff.mp (automorphismImage_le_centralizer S a.symm A (Campbell.F H)
        (hAR.trans core_thompson_centralizes_F)))
  · obtain ⟨T,hT,_⟩ := h.sylow
    exact hB.trans (inf_le_left.trans ((pCore_isPGroup.le_sylow_of_normal T).trans
      (hT.symm.trans (range_subtype S)).le))

include h hA hAR hAaR in
 theorem common_maxima_in_sylow : elementaryAbelianMaxSubgroups (commonCore S a) ⊆
    elementaryAbelianMaxSubgroups S := by
  have hw := common_maximum S h a A hA hAR hAaR
  have has := automorphismImage_maxElementary S a.symm A hA
  intro B hb
  refine ⟨hb.1.trans ?_,hb.2.1,fun C hc hce => (has.2.2 C hc hce).trans ?_⟩
  · obtain ⟨T,hT,_⟩ := h.sylow
    exact inf_le_left.trans ((pCore_isPGroup.le_sylow_of_normal T).trans
      (hT.symm.trans (range_subtype S)).le)
  · exact hb.2.2 _ hw.1 hw.2.1

include h hB hA hAR hAaR in
 theorem common_thompson_bounds :
    automorphismImage S a.symm A ≤ commonThompson S a ∧
    commonThompson S a ≤ Campbell.J (pCore 2 H) ∧
    automorphismImage S a (commonThompson S a) ≤ Campbell.J (pCore 2 H) := by
  have hfam := common_maxima_in_sylow S h a A hA hAR hAaR
  have hQS : pCore 2 H ≤ S := by
    obtain ⟨T,hT,_⟩ := h.sylow
    exact (pCore_isPGroup.le_sylow_of_normal T).trans
      (hT.symm.trans (range_subtype S)).le
  have hFS := Campbell.F_le_pCore.trans hQS
  refine ⟨le_sSup (common_maximum S h a A hA hAR hAaR),?_,?_⟩
  · exact sSup_le fun B hb => le_sSup
      ⟨hb.1.trans inf_le_left,hb.2.1,fun C hc hce => (hfam hb).2.2 C (hc.trans hQS) hce⟩
  · have hR : Campbell.J (pCore 2 H) ≤ S := (sSup_le fun _ hb => hb.1).trans hQS
    have hpre : commonThompson S a ≤ automorphismImage S a.symm (Campbell.J (pCore 2 H)) := by
      apply sSup_le
      intro B hb
      have hba := automorphismImage_maxElementary S a B (hfam hb)
      have hbc : B ≤ centralizer (imageF S a.symm : Set H) :=
        hb.1.trans (inf_le_right.trans (centralizer_le (show imageF S a.symm ≤
          Campbell.F H ⊔ imageF S a.symm from le_sup_right)))
      have hac := automorphismImage_le_centralizer S a B (imageF S a.symm) hbc
      change automorphismImage S a B ≤ centralizer
        (automorphismImage S a (automorphismImage S a.symm (Campbell.F H)) : Set H) at hac
      have heF := automorphismImage_symm S a.symm (Campbell.F H) hFS
      simp only [MulEquiv.symm_symm] at heF
      rw [heF] at hac
      have haq := (le_inf hba.1 hac).trans (core_point_centralizer S h hB)
      have har : automorphismImage S a B ≤ Campbell.J (pCore 2 H) :=
        le_sSup ⟨haq,hba.2.1,fun C hc hce => hba.2.2 C (hc.trans hQS) hce⟩
      have hh := automorphismImage_mono S a.symm har
      rwa [automorphismImage_symm S a B (hfam hb).1] at hh
    have hh := automorphismImage_mono S a hpre
    have heR := automorphismImage_symm S a.symm (Campbell.J (pCore 2 H)) hR
    simp only [MulEquiv.symm_symm] at heR
    rwa [heR] at hh

theorem common_thompson_bounds_of_contains_imageF
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hAQ : A ≤ pCore 2 H) (hFA : imageF S a ≤ A) :
    automorphismImage S a.symm A ≤ commonThompson S a ∧
      commonThompson S a ≤ Campbell.J (pCore 2 H) ∧
      automorphismImage S a (commonThompson S a) ≤ Campbell.J (pCore 2 H) := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hQS : pCore 2 H ≤ S := (pCore_isPGroup.le_sylow_of_normal T).trans
    (hT.symm.trans (range_subtype S)).le
  have hAR : A ≤ Campbell.J (pCore 2 H) :=
    le_sSup ⟨hAQ,hA.2.1,fun C hc hce => hA.2.2 C (hc.trans hQS) hce⟩
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAC : A ≤ centralizer (imageF S a : Set H) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hFA)
  have hac := automorphismImage_le_centralizer S a.symm A (imageF S a) hAC
  change automorphismImage S a.symm A ≤ centralizer
    (automorphismImage S a.symm (automorphismImage S a (Campbell.F H)) : Set H) at hac
  rw [automorphismImage_symm S a (Campbell.F H) (Campbell.F_le_pCore.trans hQS)] at hac
  have ha := automorphismImage_maxElementary S a.symm A hA
  have haq := (le_inf ha.1 hac).trans (core_point_centralizer S h hB)
  have har : automorphismImage S a.symm A ≤ Campbell.J (pCore 2 H) :=
    le_sSup ⟨haq,ha.2.1,fun C hc hce => ha.2.2 C (hc.trans hQS) hce⟩
  exact common_thompson_bounds S h hB a A hA hAR har

omit [Finite H] in
theorem common_thompson_normalized (a : MulAut S) (E : Subgroup H)
    (hE : E ≤ normalizer ((Campbell.F H ⊔ imageF S a.symm : Subgroup H) : Set H)) :
    E ≤ normalizer (commonThompson S a : Set H) := by
  have hec : E ≤ normalizer (commonCore S a : Set H) :=
    (le_inf le_normalizer_of_normal
      (hE.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ (commonCore S a)).map (MulAut.conj g).toMonoidHom = _
  have hc : (commonCore S a).map (MulAut.conj g).toMonoidHom = commonCore S a :=
    mem_normalizer_iff_map_conj_eq.mp (hec hg)
  rw [←elementaryAbelianMaxJ_map_equiv,hc]
  rfl
end CampbellTheoremA
end CFSG.Quasithin.ChapterC.GlaubermanNiles
