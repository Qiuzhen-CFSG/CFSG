module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.NoncontainmentSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Invariance
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.MixedReplacementTransport
/-!
# Campbell Theorem A for the original Sylow automorphisms

A hypothetical failed commutator bound supplies the original maximum
subgroup and involution. The mixed actor escapes the second replacement.
Its nonzero commutator is the conjugate fixed layer and is A-invariant,
contradicting the unique maximal normalizer bound. All earlier mixed-word
and maximum-family inputs are discharged by their source producers.
Source: Campbell II.6–7, printed pp.31–36; Aschbacher–Smith C.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.campbell_theoremA
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (hAll : ∀ a : MulAut S, automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    ∀ a : MulAut S, ⁅Campbell.J (⊤ : Subgroup H),automorphismImage S a (Campbell.F H)⁆ ≤ Campbell.F H := by
  intro a
  by_contra hn
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hF : ¬imageF S a ≤ Campbell.F H := fun hf => hn ((commutator_mono le_rfl hf).trans (commutator_le_right _ _))
  obtain ⟨M,A,g,hSM,hMt,hNZ,hA,hAQ,hgK,hg2,hgM⟩ := h.exists_theoremA_actors S hB
  have hM : S ≤ M ∧ M ⋖ ⊤ := ⟨hSM,hMt⟩
  have hnon := h.mixedActor_not_le_replacement S hB a hAll hn A hA hAQ M hM hNZ g hgK hg2 hgM
  let B := replacement S a A g
  let Y := mixedActor S a g
  have ht := h.mixed_replacement_maximum_and_commutator S hB a hAll hF A hA g hgK hg2
  have hBn := h.mixed_commutator_normalized_of_maximum S hB a hAll hF A hA hAQ M hM g hgK hg2 hgM ht.1
  have hcomm : ⁅B,Y⁆=(fixed S).map (MulAut.conj g).toMonoidHom := by
    rcases ht.2.2 with hb | he
    · have hBY : B ≤ centralizer (Y : Set H) := commutator_eq_bot_iff_le_centralizer.mp hb
      have hW0 : Y ⊔ (B ⊓ centralizer (Y : Set H)) ∈ elementaryAbelianMaxSubgroups S := ht.1
      have hW : Y ⊔ B ∈ elementaryAbelianMaxSubgroups S := by
        simpa only [inf_eq_left.mpr hBY] using hW0
      have hb0 := h.replacement_geometry S hB a hAll A hA g
      have he : B=Y ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (hb0.1.2.2 _ hW.1 hW.2.1)
      exact False.elim (hnon (le_sup_left.trans he.symm.le))
    · exact he
  have hAn : A ≤ normalizer ((fixed S).map (MulAut.conj g).toMonoidHom : Set H) := by
    change A ≤ normalizer ((⁅B,Y⁆ : Subgroup H) : Set H) at hBn
    rwa [hcomm] at hBn
  have hAgn : A.map (MulAut.conj g).toMonoidHom ≤ normalizer (fixed S : Set H) := by
    have hm := (map_mono (f:=(MulAut.conj g).toMonoidHom) hAn).trans (le_normalizer_map (MulAut.conj g).toMonoidHom)
    rwa [conj_twice g hg2] at hm
  obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hAQ
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hs : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn',k,_,_,_,hk,⟨m⟩⟩ := h.natural
  exact h.campbell_maximal_separation hB m d hS M (by rwa [hs]) g x hgM
    (by change x∈(d.sylow:Subgroup H);rw [hs];exact hA.1 hx) hxQ
    (hNZ (hAgn (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)))
end CFSG.Quasithin.ChapterC.GlaubermanNiles
