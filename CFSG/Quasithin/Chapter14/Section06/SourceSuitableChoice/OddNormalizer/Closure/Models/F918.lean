module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Orbit
public import CFSG.Quasithin.Chapter14.Section06.SourcePlacedQuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.PairedActor
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Swapped

/-!
# The F.9.18 component lists on the original odd closure

Restrict to the join of the detected component orbit and the given Sylow
subgroup. The intrinsic complement generates the original residual, so the
join contains the original outside H and is itself outside M. Its faithful
placed quadratic actor therefore supplies the F.9.18 list. For an invariant
component A.3.6 supplies center order one or three, retaining central covers.
For exchanged components the actual index-two normalizer supplies the pair
geometry in the quotient. Every model is transported back to L/O₂(L).

This argument does not use the later hypothesis that every solvable Sylow
overgroup lies in M. The literal consumer is Models.Comparison. Primitive
and exchanged data retain qt-e-quintic-recognition and qt-e-14612-singleton;
the remaining strict comparison and final assembly stay with
qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033, applying
F.9.18(4)--(5), pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
include hG hempty hM hunique hmany hcard e hab hH

/-- F.9.18(5) for the detected exchanged component, with the original
H and its actual outside-subgroup join. -/
theorem source_swapped_closure_f918_models
    {p : ℕ} {P L : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p (T : Subgroup G) (residual H) P Mc L) :
    NonnormalF918Models (XiQuotient L) := by
  let X := componentOrbit L (T : Subgroup G)
  let J := X ⊔ (T : Subgroup G)
  have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans h.overgroup
  have hXMc : X ≤ Mc := (componentOrbit_le_sup L (T : Subgroup G)).trans
    (sup_le h.component.1 hTMc)
  have hJMc : J ≤ Mc := sup_le hXMc hTMc
  have hXJ : X ≤ J := le_sup_left
  have hLJ : L ≤ J := (le_componentOrbit L _).trans hXJ
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hHX : Mc ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXMc).mp h.orbit_normal
  have hres : residual H ≤ X := h.toLocalInput.le_of_complement_le
    h.complement_le_orbit hHX
  have hHJ : H ≤ J := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.2))
    have he : residual H ⊔ (T : Subgroup G) = H := by
      rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
      change residual H ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
      rwa [map_subgroupOf_eq_of_le hH.1.2] at hh
    rw [←he]
    exact sup_le (hres.trans le_sup_left) le_sup_right
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hMcOver : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,hTMc⟩
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨Chapter3.mem_HOver_of_sylow_interval T hTJ hJMc
      hMcOver,
      fun hj => hH.2 (hHJ.trans hj)⟩
  have hTL := h.not_invariant
  have hc : (L.subgroupOf J).IsCComponent := h.component.2.subgroupOf_of_le hLJ hJMc
  let : Group.IsPerfect (L.subgroupOf Mc) := h.component.2.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component.1).toMonoidHom) (subgroupOfEquivOfLe h.component.1).surjective
  let : Group.IsPerfect X := by
    rw [show X = conjugateSpanBy L (T : Subgroup G) from
      (conjugateSpanBy_eq_iSup_conj L (T : Subgroup G)).symm]
    exact conjugateSpanBy_isPerfect L (T : Subgroup G)
  let : Group.IsPerfect (X.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXJ).symm.toMonoidHom) (subgroupOfEquivOfLe hXJ).symm.surjective
  let : (X.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr (hJMc.trans hHX)
  have hp : IsPPerfect 2 (X.subgroupOf J) := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial ((X.subgroupOf J) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent ((X.subgroupOf J) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((X.subgroupOf J) ⧸ N) inferInstance
  have hr : pResidual 2 J = X.subgroupOf J :=
    pResidual_eq_of_isPPerfect_sup (X.subgroupOf J) ((T : Subgroup G).subgroupOf J)
      hp T.isPGroup'.comap_subtype (by
        rw [←subgroupOf_sup hXJ hTJ]
        change J.subgroupOf J = ⊤
        simp only [subgroupOf_self])
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,hfaith⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := (L.subgroupOf J).map q
  let S := ((T : Subgroup G).subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hmove : ¬ S ≤ normalizer (D : Set (J ⧸ pCore 2 J)) := by
    intro hsn
    have ht := map_le_iff_le_comap.mp hsn
    rw [normalizer_cComponent_quotient hc (pCore 2 J)] at ht
    apply hTL
    intro t htt
    have ht' := ht (show (⟨t,hTJ htt⟩ : J) ∈ (T : Subgroup G).subgroupOf J from htt)
    rwa [←subgroupOf_normalizer_eq hLJ] at ht'
  obtain ⟨hi,hm⟩ : (normalizer (D : Set (J ⧸ pCore 2 J))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel D := by
    rcases ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple hs
      (pCore_quotient_pCore_eq_bot 2) D (hc.map_quotient (pCore 2 J)) with hdn | hm
    · let := hdn
      exact (hmove (by rw [normalizer_eq_top]; exact le_top)).elim
    · exact hm
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv ec
  have hD : IsComponent (J ⧸ pCore 2 J) D :=
    ⟨(hc.map_quotient (pCore 2 J)).subnormal,inferInstance⟩
  have hAT : A.map q ≤ S := by
    apply map_mono
    have hTI : (T : Subgroup G) ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ J :=
      le_inf le_sup_right hTJ
    have hcore := pCoreIn_le_sylow _ (T.subtype hTI)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] at hcore
    exact hA.trans (subgroupOf_mono J hcore)
  have hX : X.subgroupOf J = conjugateSpanBy (L.subgroupOf J) ((T : Subgroup G).subgroupOf J) := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hXJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hLJ,map_subgroupOf_eq_of_le hTJ,conjugateSpanBy_eq_iSup_conj]
    rfl
  have hfaith' : A.map q ⊓ centralizer (componentOrbit D S : Set (J ⧸ pCore 2 J)) = ⊥ := by
    rw [GenerationOne.residual,hr,actorImage_internal,hX,map_conjugateSpanBy,
      conjugateSpanBy_eq_iSup_conj] at hfaith
    exact hfaith
  exact (nonnormal_models_of_quadratic_actor a.representation D S (A.map q) hD hs hm hi
    hmove a.faithful hAT hAE hAQ hbound hfaith').transport ec

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer

namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
include hG hempty hM hunique hmany hcard e hab hH

/-- The normal-component F.9.18 list on the original strict orbit join.
The literal residual containment places H inside KT, and A.3.6 supplies the
center order needed by the quadratic-actor theorem, including cubic covers. -/
theorem source_invariant_closure_f918_models
    {p : ℕ} {P K : Subgroup G}
    (h : LocalInput p (T : Subgroup G) (residual H) P Mc)
    (hKH : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient K)) (hn : (K.subgroupOf Mc).Normal)
    (hPK : P ≤ K) : F918Models (XiQuotient K) := by
  let J := K ⊔ (T : Subgroup G)
  have hJMc : J ≤ Mc := sup_le hKH (le_sup_right.trans h.overgroup)
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hres : residual H ≤ K := h.le_of_complement_le hPK
    ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hHJ : H ≤ J := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change residual H ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rw [map_subgroupOf_eq_of_le hH.1.2] at hh
    rw [←hh]
    exact sup_le (hres.trans le_sup_left) le_sup_right
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hMcOver : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,
      show (T : Subgroup G) ≤ Mc from le_sup_right.trans h.overgroup⟩
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨Chapter3.mem_HOver_of_sylow_interval T hTJ hJMc hMcOver,
      fun hj => hH.2 (hHJ.trans hj)⟩
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJMc
  have hnc : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJMc.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    change J.subgroupOf J = ⊤
    simp only [subgroupOf_self]
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,_⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  let D := (K.subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
  let : IsQuasisimple (XiQuotient K) := hq
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv ec
  let : D.Normal := hnc.map q (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  have hAD : A.map q ⊓ centralizer (D : Set (J ⧸ pCore 2 J)) = ⊥ :=
    source_placed_actor_faithful_on_normal_cComponent T hTJ A hA
      (K.subgroupOf J) hc hnc hgen
  apply f918Models_transport ec
  have hcommon := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    _ hs (pCore_quotient_pCore_eq_bot 2) D (hc.map_quotient (pCore 2 J))
  have hcenter := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common hcommon.2
  exact f918Models_of_quadratic_actor a.representation D (A.map q) a.faithful
    hcenter hs hAE hAQ hbound hAD

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
