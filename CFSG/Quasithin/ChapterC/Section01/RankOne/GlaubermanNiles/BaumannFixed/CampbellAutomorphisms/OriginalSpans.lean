module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.Involutions
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.OriginalMarkings
/-!
# Campbell's core-span bounds on the original local markings

The common elementary Thompson subgroup of the actual Baumann group
identifies Campbell transfer with pullback under e′ followed by image
under e. Thus the core, commutator and Frattini bounds for the conjugate
span use precisely the original marked local groups; both natural
models and the intermediate embeddings are constructed internally.
Source: Campbell, II.6.1, printed p.29, in the C.1.18 application.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H H' : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group H'] [Finite H']
  {e : B →* H} {e' : B →* H'}
omit [Finite B] [Finite H] in
private theorem marking_transfer (h' : InLocalClass e')
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


theorem InLocalClass.original_span_core_frattini (h : InLocalClass e)
    (h' : InLocalClass e') (hB : IsBaumannFixed B)
    (hV : ((Campbell.V H').comap e').map e ≤ pCore 2 H) :
    let Y := ((Campbell.F H').comap e').map e
    let Z := ((Campbell.V H' ⊓ centralizer (e'.range : Set H')).comap e').map e
    let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
    W ≤ Campbell.J (pCore 2 H) ∧ ⁅W,Campbell.J (pCore 2 H)⁆ ≤ Z ∧
      (frattini W).map W.subtype ≤ Z := by
  obtain ⟨d,hd,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨d',hd',hS'⟩ := h'.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  obtain ⟨n',hn',F',_,_,_,hcard',⟨m'⟩⟩ := h'.natural
  have ht := h'.campbell_marked_containments hB d'
  have htf := marking_transfer h' d d' hd hd' _ ht.1
  have htv := marking_transfer h' d d' hd hd' _ ht.2.1
  have htz := marking_transfer h' d d' hd hd'
    (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) (inf_le_left.trans ht.2.1)
  have hh := h.paired_span_core_frattini_all hB m h' hB m' d d' hS hS' (htv.symm ▸ hV)
  dsimp only at hh ⊢
  rw [htf,htz] at hh
  have hSet : (d'.sylow : Set H') = (e'.range : Set H') := congrArg (fun X : Subgroup H' => (X : Set H')) hS'
  rw [hSet] at hh
  exact hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles
