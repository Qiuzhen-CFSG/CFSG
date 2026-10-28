module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenEvenModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenOdd
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
/-!
# Alternating-seven maximality on the actual larger source image

The known-simple containing catalogue reduces an A7 local component to
itself. Rank-two and rank-one nonenlargement handle the classical rows;
the intrinsic Sylow action and odd ternary involution centralizers close
the exceptional rows. The literal source application places the image
inside its normal containing component, so equality proves normality in
X/O₂(X), with no universal A.3.12 assumption.
Source: Aschbacher–Smith A.3.12 and C.5.12, printed pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private theorem seven_quasisimple {B : Type*} [Group B] (hB : IsAlternating B 7) : IsQuasisimple B := by
  let : Group.IsPerfect B := AlternatingSevenMaximal.perfect_of_model hB
  let : IsSimpleGroup B := AlternatingSevenMaximal.simple_of_model hB
  refine ⟨?_⟩
  let e := (QuotientGroup.quotientMulEquivOfEq (AlternatingSevenMaximal.center_of_model hB)).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup

private theorem seven_rank {B : Type*} [Group B] [Finite B] (hB : IsAlternating B 7) : 2 ≤ primeRank 2 B := by
  rw [primeRank_equiv 2 hB.some,Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating]

private theorem eq_of_seven_cover {B L : Subgroup G} (hBL : B ≤ L)
    (hB : IsAlternating B 7) (hL : IsAlternatingCover L 7) : B=L := by
  obtain ⟨hq,⟨ec⟩,⟨eq⟩⟩ := hL
  let : IsQuasisimple L := hq
  have hcard : Nat.card L=7560 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L),Nat.card_congr eq.toEquiv,
      Nat.card_congr ec.toEquiv,nat_card_alternatingGroup]
    norm_num
  let C := B.subgroupOf L
  have hc : Nat.card C=2520 := (Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv).trans
    (AlternatingSevenMaximal.card_of_model hB)
  have hi : C.index ≤ 4 := by have hh := C.card_mul_index; rw [hc,hcard] at hh; omega
  have ht : C=⊤ := by
    let : Group.IsPerfect (⊤ : Subgroup L) :=
      Group.IsPerfect.ofSurjective (f := (topEquiv (G := L)).symm.toMonoidHom) (topEquiv (G := L)).symm.surjective
    exact top_unique (le_of_isPerfect_of_index_le_four ⊤ C hi)
  exact le_antisymm hBL (subgroupOf_eq_top.mp ht)

theorem seven_larger_eq_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G=⊥)
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hmodel : IsAlternating B 7) : B=L := by
  let : IsQuasisimple B := seven_quasisimple hmodel
  let : IsQuasisimple L := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hG hO hL
    ((seven_rank hmodel).trans (primeRank_mono 2 hBL))
  obtain ⟨S,_,hloc,hnorm⟩ := exists_local_sylow_normalizing T hB hL.subnormal hBL hTB
  let : IsQuasisimple (B.subgroupOf L) := quasisimple_subgroupOf hBL
  have hsmall : IsAlternating (B.subgroupOf L) 7 := ⟨(subgroupOfEquivOfLe hBL).trans hmodel.some⟩
  have hmodels := quasisimple_containing_component_models_knownSimple hG hO hL
  rcases hmodels with ⟨_,hs⟩ | ⟨_,hs⟩
  · cases hs with
    | alternating d hd hm =>
        have hd' : d=5 ∨ d=6 ∨ d=7 ∨ d=8 := by omega
        rcases hd' with rfl | rfl | rfl | rfl
        · exact eq_of_small_alternating_containing_component T hB hL hBL (.inl hm)
        · exact eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inl hm))
        · exact eq_of_le_of_card_ge hBL (by rw [AlternatingSevenMaximal.card_of_model hm,
            AlternatingSevenMaximal.card_of_model hmodel])
        · apply eq_of_binary_linear_four_or_five T hB hL hBL (.inl rfl)
          obtain ⟨e⟩ := hm
          exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
            ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
    | linear_odd p e hp ho he _ hm =>
        by_contra hne
        rcases he with rfl | rfl
        · have hm' : ClassicalGroup.IsPSL L 2 p := by simpa only [pow_one] using hm
          obtain ⟨_,hb⟩ := proper_primePSL2_models T hB hL hBL hne hp ho hm'
          exact AlternatingSevenMaximal.not_alternating_five hmodel hb
        · obtain ⟨_,hb⟩ := proper_quadraticPSL2_models T hB hL hBL hne hp ho hm
          exact AlternatingSevenMaximal.not_odd_linear_two hmodel hp ho hb
    | three_odd p hp ho u hm =>
        exact ((not_seven_local_odd_three S hnorm hsmall hp ho u).1 hm).elim
    | rank_one hm => exact eq_of_bender_containing_component T hB hL hBL hm
    | rank_two hm =>
        cases hm with
        | linear m hm he => exact eq_of_binary_linear_three_model T hB hL hBL hm he
        | symplectic m hm he => exact eq_of_binary_symplectic_model T hB hL hBL hm he
        | g2 _ _ he => exact eq_of_binary_g2_model T hB hL hBL he
        | triality _ hm he => exact (not_seven_local_triality S hloc hnorm hsmall hm he).elim
        | ree _ hm he => exact (not_seven_local_ree S hloc hnorm hsmall hm he).elim
        | symplectic_derived he => exact eq_of_binary_symplectic_derived_model T hB hL hBL he
        | g2_derived he => exact eq_of_binary_g2_derived_model T hB hL hBL he
        | tits he => exact eq_of_tits_model T hB hL hBL he
    | binary_linear d hd hm => exact eq_of_binary_linear_four_or_five T hB hL hBL hd hm
    | sporadic name hne hm => exact (not_seven_local_sporadic S hloc hnorm hsmall name hne hm).elim
    | janko_one hm =>
        obtain ⟨e⟩ := hm
        have hd := card_dvd_of_le hBL
        rw [AlternatingSevenMaximal.card_of_model hmodel,Nat.card_congr e.toEquiv,Janko1.card_model] at hd
        norm_num at hd
  · cases hs with
    | classical u q hq hm =>
        rcases hq with ⟨m,hm,rfl,_⟩ | ⟨hp,ho⟩
        · cases u with
          | false => exact eq_of_binary_special_linear_three_model T hB hL hBL (by omega) hm
          | true => exact eq_of_binary_su3_containing_component T hB hL hBL (by omega) hm
        · exact ((not_seven_local_odd_three S hnorm hsmall hp ho u).2 hm).elim
    | alternating_six hm => exact eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inr hm))
    | alternating_seven hm => exact eq_of_seven_cover hBL hmodel hm
    | mathieu hm => exact (not_seven_local_m22_cover S hloc hnorm hsmall hm).elim

open ConjugateSource.RankOne

theorem source_larger_A7_image_normal_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsAlternating (((conjugateSpanBy K N).subgroupOf X).map
        (QuotientGroup.mk' (pCore 2 X))) 7) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    (((conjugateSpanBy K N).subgroupOf X).map
      (QuotientGroup.mk' (pCore 2 X))).Normal := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (L.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  obtain ⟨hlocal,hTL⟩ := source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS
  have hLX : L ≤ X := hlocal.1
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : L.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hLX).mp hlocal
  have hB : B ∈ ChapterA.Section03.localCComponents Q := mem_L_map_twoCore_mem_localCComponents hmem
  have hTB : (Q : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set (X ⧸ pCore 2 X)) := by
    have hn : (S : Subgroup X) ≤ normalizer (L.subgroupOf X : Set X) := by
      rw [← hTs,← subgroupOf_normalizer_eq hLX]
      exact comap_mono hTL
    exact (map_mono hn).trans (le_normalizer_map r)
  obtain ⟨D,hD,hLD,_,hn⟩ := source_larger_normal_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let : D.Normal := hn
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : (D.map r).IsCComponent := hD.map_quotient (pCore 2 X)
  have hSQTK := source_larger_quotient_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS
  have he : B=D.map r := seven_larger_eq_knownSimple hSQTK (pCore_quotient_pCore_eq_bot 2)
    Q hB hE (map_mono hLD) hTB hmodel
  change B.Normal
  rw [he]
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
