module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotientsSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisSylowResidualsQuotientsSource at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsQuotientsSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

include E

theorem seven_twoCore_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) := by
  let H := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf H
  let U := V.subgroupOf H
  have hVH : V ≤ H := S.chosen.le_component.trans le_sup_left
  let eB : B ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let := S.hypothesis.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
  have hB : B.IsCComponent := S.hypothesis.maximal_faithful.1.1.1
  have hchar : HasCharacteristicTwo H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨S.hypothesis.maximal_faithful.1.1.2.2,
        fun x hx => (le_sup_right : (T : Subgroup G) ≤ H) hx⟩)
  have hfH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  have hfB : generalizedFitting B = pCore 2 B :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing hchar B hB.subnormal)
  have hred : IsPReduced 2 U := ((structural L S.hypothesis).2.2 V S.chosen).2.1
  let : U.Normal := hred.normal
  let : IsElementaryAbelian 2 U := hred.elementary
  let : IsElementaryAbelian 2 V := S.chosen.elementary
  have hm : ⁅U,B⁆ = U := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVH,
      map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)]
    exact S.chosen.eq_commutator.symm
  have hUne : U ≠ ⊥ := by
    intro hu
    have he := congrArg (map H.subtype) hu
    rw [map_subgroupOf_eq_of_le hVH, Subgroup.map_bot] at he
    exact S.chosen.ne_bot he
  obtain ⟨P,hP⟩ := S.hypothesis.maximal_faithful.1.1.2.1
  have hPT : (P : Subgroup H) = (T : Subgroup G).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hprod : ∀ g : H, ∃ b ∈ B, ∃ t ∈ (P : Subgroup H), b*t=g := by
    intro g
    have hg : (g : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
        S.chosen.sylow_normalizes_component]
      exact g.property
    obtain ⟨b,hb,t,ht,hbt⟩ := Set.mem_mul.mp hg
    refine ⟨⟨b,(show L ≤ H from le_sup_left) hb⟩,hb,
      ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩,?_,Subtype.ext hbt⟩
    rw [hPT]
    exact ht
  have hHV : H ≤ normalizer (V : Set G) := sup_le S.chosen.normalizes
    (((structural L S.hypothesis).2.2 V S.chosen).1)
  let D := E.sourceNormalizerModel_at structural
  let q : H →* Equiv.Perm (Fin 7) := D.permutation.comp (inclusion hHV)
  let eU : U ≃* V := subgroupOfEquivOfLe hVH
  let ea : Additive U ≃+ EvenWord := (eU.trans E.coordinates).toAdditive
  let e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    (ea.toLinearEquiv (fun c x => ZMod.map_smul ea.toAddMonoidHom c x)).trans
      evenWordsEquivNatural
  have he : ∀ (g : H) (v : Additive U),
      e (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        BinaryPermutation.naturalRepresentation (Fin 7) (q g) (e v) := by
    intro g v
    change evenWordsEquivNatural (E.coordinates (eU (MulAut.conjNormal g v.toMul))).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 7) (q g)
        (evenWordsEquivNatural (E.coordinates (eU v.toMul)).toAdd)
    rw [← evenWordsEquivNatural_equivariant]
    congr 1
    exact D.equivariant ⟨g,hHV g.property⟩ (eU v.toMul)
  have hk : q.ker = centralizer (U : Set H) := by
    ext g
    constructor
    · intro hg u hu
      have he' := D.equivariant ⟨g,hHV g.property⟩ (eU ⟨u,hu⟩)
      change _ = evenRepresentation (q g) _ at he'
      rw [show q g = 1 from hg, map_one] at he'
      have hh := D.coordinates.injective (Multiplicative.toAdd.injective he')
      apply H.subtype_injective
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
    · intro hg
      apply D.permutation_eq_one_of_centralizes_simplex ⟨g,hHV g.property⟩
      intro v hv
      have hvV := D.simplex_le hv
      have hc := hg ⟨v,hVH hvV⟩ hvV
      exact congrArg H.subtype hc
  have hBq : B.map q = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have hp := E.sourceNormalizerModel_component_at structural (eB ⟨l,hl⟩)
      change q l = _ at hp
      rw [hp]
      exact (S.projection (eB ⟨l,hl⟩)).property
    · intro a ha
      obtain ⟨l,hl⟩ := S.projection_surjective ⟨a,ha⟩
      refine ⟨⟨l,(show L ≤ H from le_sup_left) l.property⟩,l.property,?_⟩
      exact (E.sourceNormalizerModel_component_at structural l).trans (congrArg Subtype.val hl)
  have hcore : pCore 2 H = (P : Subgroup H) ⊓ centralizer (U : Set H) := by
    have hc := RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural
    apply map_injective H.subtype_injective
    change H.pCoreIn 2 = _
    rw [← hc, map_inf _ _ _ H.subtype_injective, hP]
    ext x
    constructor
    · rintro ⟨hxT,hxc⟩
      refine ⟨hxT,⟨⟨x,(show (T : Subgroup G) ≤ H from le_sup_right) hxT⟩,?_,rfl⟩⟩
      intro u hu
      exact H.subtype_injective (hxc u hu)
    · rintro ⟨hxT,y,hy,rfl⟩
      refine ⟨hxT,?_⟩
      intro v hv
      exact congrArg H.subtype (hy ⟨v,hVH hv⟩ hv)
  have hb := SylowNormalizer.block_of_natural_seven_action B U hB hfH hfB P hprod
    q hk hBq e he (hm.symm ▸ hUne) hcore
    (fun C hC hn => by
      let : C.Characteristic := hC
      exact SylowNormalizer.no_characteristic_baumann_join S hescape P hP C hn)
  exact ⟨eQ.symm.trans
    ((ChapterC.RankOne.SevenSource.coreQuotientEquiv_of_full_moved B U hb hUne hm q hk).trans
      (MulEquiv.subgroupCongr hBq))⟩

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

