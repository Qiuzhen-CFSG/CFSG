module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.Source


/-!
# Campbell comparison on the original Sylow markings

Two members of C.1.17 marked by the same Baumann-fixed two-group share
its actual elementary Thompson subgroup. Constructing those Campbell
embeddings and using their proved containments identifies every transfer
with the literal pullback under e′ followed by image under e.
The final theorem takes only the two original local-class hypotheses,
Baumann fixedness and the comparison's V/F containments; natural models
and auxiliary Thompson embeddings are constructed internally.
Source: Campbell, *Pushing up in Finite Groups* (1979), Theorem B,
printed pp.14 and 27–29, in the C.1.18 uniform-family application.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H H' : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group H'] [Finite H']
  {e : B →* H} {e' : B →* H'}

omit [Finite B] [Finite H] in
private theorem original_transfer (h' : InLocalClass e')
    (d : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H)
    (d' : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H')
    (hd : d.marking = e.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype)
    (hd' : d'.marking = e'.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype)
    (X : Subgroup H') (hX : X ≤ d'.marking.range) :
    d.transfer d' X = (X.comap e').map e := by
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨j.val,?_,?_⟩
    · change e' j.val ∈ X
      change d'.marking j ∈ X at hj
      rwa [hd'] at hj
    · rw [hd]; rfl
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨j,hj⟩ := hX hb
    have hjb : (j : B)=b := h'.injective (by simpa only [hd',MonoidHom.comp_apply,coe_subtype] using hj)
    refine ⟨j,?_,?_⟩
    · change d'.marking j ∈ X
      rw [hj]
      exact hb
    · rw [hd]
      change e j.val = e b
      rw [hjb]

theorem InLocalClass.campbell_comparison_original_markings (h : InLocalClass e) (h' : InLocalClass e') (hB : IsBaumannFixed B)
    (hV : ((Campbell.V H').comap e').map e ≤ pCore 2 H)
    (hF : ¬ ((Campbell.F H').comap e').map e ≤ Campbell.F H) :
    ((⁅e'.range,Campbell.V H'⁆).comap e').map e ≤
      (center (Campbell.J (⊤ : Subgroup H))).map (Campbell.J (⊤ : Subgroup H)).subtype := by
  obtain ⟨d,hd,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨d',hd',hS'⟩ := h'.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  obtain ⟨n',hn',F',_,_,_,hcard',⟨m'⟩⟩ := h'.natural
  have hc := h.campbell_comparison hB m h' hB m' d d' hS hS'
  have ht := h'.campbell_marked_containments hB d'
  rw [←original_transfer h' d d' hd hd' _ ht.2.1] at hV
  rw [←original_transfer h' d d' hd hd' _ ht.1] at hF
  have hh := hc hV hF
  rw [original_transfer h' d d' hd hd' _ ht.2.2,hS'] at hh
  exact hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles
