module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.ConjugateControl
/-!
# Campbell II.6.3 actor and full-layer commutation

The point-centralizer theorem is first upgraded through the common Thompson
marking: original transfers identify the natural module, its F-layer and
all conjugates. Hence the checked natural commutation theorem applies to
the actual α∈Aut(S) span, then to the original marked source transfer.
The final exported theorem supplies the source's full actor statement:
for every transported natural actor in V and every J(H)-conjugate,
the corresponding F-conjugates commute. No arbitrary ambient automorphism
extension or model classification is assumed.
Source: Campbell II.6.3, printed pp.30–31, and C.1.18's Aut(S) corollary.
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


theorem InLocalClass.original_conjugates_commute_of_natural (h : InLocalClass e) (h' : InLocalClass e')
    (hB : IsBaumannFixed B) (hV : ((Campbell.V H').comap e').map e ≤ pCore 2 H) (g k:H)
    (hc : ⁅(((Campbell.V H').comap e').map e).map (MulAut.conj g).toMonoidHom,
      (((Campbell.V H').comap e').map e).map (MulAut.conj k).toMonoidHom⁆=⊥) :
    ⁅(((Campbell.F H').comap e').map e).map (MulAut.conj g).toMonoidHom,
      (((Campbell.F H').comap e').map e).map (MulAut.conj k).toMonoidHom⁆=⊥ := by
  obtain ⟨d,hd,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨d',hd',hS'⟩ := h'.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  obtain ⟨n',hn',F',_,_,_,hcard',⟨m'⟩⟩ := h'.natural
  have ht := h'.campbell_marked_containments hB d'
  have htf := marking_transfer h' d d' hd hd' _ ht.1
  have htv := marking_transfer h' d d' hd hd' _ ht.2.1
  have hh := h.paired_conjugates_commute_of_natural hB m h' hB m' d d' (htv.symm ▸ hV) g k
    (by rwa [htv])
  rwa [htf] at hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem transfer_sylow_aut (a : MulAut S) (X : Subgroup H) :
    (X.comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype =
      automorphismImage S a X := by
  rw [←comap_comap,comap_equiv_eq_map_symm']
  rfl

omit [Finite H] in
private theorem conjugate_map_mul (A : Subgroup H) (x g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply,mul_assoc]

theorem InLocalClass.sylow_automorphism_full_actor_conjugates (hL : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    let W := conjugateSpanBy (automorphismImage S a (Campbell.F H)) (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    ∃ b : W' ≃* W,
      (∀ w : W', (b w : H) = (a ⟨w,automorphismImage_le S a.symm W w.property⟩ : H)) ∧
      ∀ u : normalizer (W : Set H), (u : H) ∈ Campbell.J (⊤ : Subgroup H) →
        ∀ x : W', spanConjugationMap W W' b u x ∈ Campbell.V H →
          ∀ g ∈ Campbell.J (⊤ : Subgroup H),
            let A := (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom
            ⁅A,A.map (MulAut.conj (x:H)).toMonoidHom⁆=⊥ := by
  obtain ⟨b,hb,hc⟩ := hL.sylow_automorphism_actor_conjugates S hB a hV
  refine ⟨b,hb,?_⟩
  intro u hu x hx g hg
  have hn := hc u hu x hx g hg
  dsimp only at hn ⊢
  rw [conjugate_map_mul] at hn ⊢
  have h' := hL.precomp_equiv a.symm
  have hv : ((Campbell.V H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ pCore 2 H := by
    rwa [transfer_sylow_aut]
  have hh := hL.original_conjugates_commute_of_natural h' hB hv g ((x:H)*g)
    (by simpa only [transfer_sylow_aut] using hn)
  simpa only [transfer_sylow_aut] using hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles
