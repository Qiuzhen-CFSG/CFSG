module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.PushingUp
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.RankTwoExclusion
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# The actual components in Mathieu residual pushing up

The proved generalized-Fitting escape selects an escaping C-component in
H. In the ordinary branch, the original intersection residual and full
module lie in that same normal component. The original V embeds in its
central quotient: an element of V centralizing the residual centralizes L,
because the residual covers L modulo its two-core and that core centralizes
V. The actual non-FF fixed-space theorem makes this kernel trivial.

The Mathieu rank bound and existing two-local exclusions now leave the J₄
central quotient, retaining the entire ordinary component. In the constrained
branch, the unchanged radical and component supply the literal C.2.7 input
and its proved star model. The Hall consumer constructs this alternative
without a residual-uniqueness, Fitting-escape or model-placement callback.
The constrained exclusion and both J₄ ambient arguments remain open.

Source: Aschbacher--Smith, C.2.11--13, C.3.2--4 and C.4.4, printed pp.148--152;
4.2.5, 4.2.12--13 and 4.4.14, printed pp.609--612 and 624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
include D in
private theorem residual_module_quotient_injective
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {F K : Subgroup G} (hVK : V ≤ K) (hFK : F ≤ K)
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G)) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp (inclusion hVK)) := by
  let f := (QuotientGroup.mk' (center K)).comp (inclusion hVK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : inclusion hVK x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hxc : (x : G) ∈ centralizer (F : Set G) := by
    intro y hy
    exact congrArg K.subtype (mem_center_iff.mp hz (inclusion hFK ⟨y,hy⟩))
  have hxl : (x : G) ∈ centralizer (L : Set G) := by
    intro y hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hcover ▸ (show y ∈ (L : Set G) from hy)
    calc
      (a * b) * (x : G) = a * (b * x) := mul_assoc _ _ _
      _ = a * (x * b) := congrArg (a * ·) ((hcore hb) x x.property).symm
      _ = x * (a * b) := by rw [←mul_assoc,hxc a ha,mul_assoc]
  apply Subtype.ext
  exact (show (x : G) ∈ (⊥ : Subgroup G) from hfix ▸ ⟨x.property,hxl⟩)

/-- In the actual pushing-up branch an ordinary component can only have
central quotient J4. The original V survives injectively in that quotient,
since its residual covers L and V has no L-fixed points. -/
theorem sourceOrbit_mathieu_pushingUp_ordinary_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVK : V ≤ Kg := hVF.trans hFK
  have hnF : F ≤ normalizer (V : Set G) := hFL.trans D.normalizes
  let := D.elementary
  have hVcore : V ≤ F.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVF hnF
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : IsQuasisimple K := hK.2
  let q : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := centerQuotientCongr q
  have hkg := hc.sqtk.subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    hkg.stronglyQuasithin.quasithin hkg.isKGroup
  have hr : 10 ≤ primeRank 2 (K ⧸ center K) := by
    have hi := D.residual_module_quotient_injective
      (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hVK hFK hcover
    have hh := (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm).trans
      (Theory.GroupTheory.primeRank_le_of_injective 2 _ hi)
    rwa [primeRank_congr 2 z] at hh
  have hnb : ¬ ClassificationModels.IsBenderModel (K ⧸ center K) := by
    intro hb
    exact no_bender_of_residual_module Kg F V hFK hVcore D.ne_bot hmove (hb.of_mulEquiv z)
  rcases rankTwo_or_jankoFour_of_mathieu_rank hmodel hr hnb with ⟨n,hrow⟩ | hj
  · exfalso
    let : Finite D.orbitComponent :=
      Finite.of_surjective D.orbitComponentHom D.orbitComponentHom_surjective
    let := D.orbitComponent_quasisimple h.toHypothesis1221
    let a := (centerQuotientCongr e).trans (D.orbitCentralQuotientEquiv h.toHypothesis1221)
    let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) := a.toMonoidHom.comp
      ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp (QuotientGroup.mk' (pCore 2 F)))
    have hπ : Function.Surjective π := a.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    exact no_rankTwo_of_mathieu_residual F Kg V hFK hVcore D.ne_bot hmove hm π hπ
      (hrow.of_mulEquiv z)
  · exact hj
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The actual pushing-up witnesses with the escaping component selected in H.
The two branches retain either ordinary-component placement or the literal
C.2.7 input and its proved star model. -/
@[expose] def MathieuPushingUpComponentCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ F ≤ normalizer (K.map H.subtype : Set G) ∧
      ((IsComponent H K ∧ K.Normal ∧ F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
          Nonempty ((K ⧸ center K) ≃* Janko4.Model)) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H (J.pCoreIn 2) M (K.map H.subtype) ∧
          ChapterC.C27Source.StarModels.Model
            (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal fixed residual supplies the component rather than assuming
an escaping generalized-Fitting component in the pushing-up branch. -/
theorem sourceOrbit_mathieu_pushingUp_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    MathieuPushingUpComponentCase L V A := by
  obtain ⟨J,H,W,hw,hf⟩ := D.sourceOrbit_mathieu_pushingUp_escape h.toHypothesis1221 hm A hAN hcomm ho hAV hnot
  have hc := hw.2.2.2.2.2.2.1
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H := by
    exact fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨K,hK,hq,hout,hn,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  refine ⟨J,H,W,hw,hf,K,hK,hq,hout,(le_conjugateSpanBy _ _).trans hn,?_⟩
  rcases hcases with ho | hfK
  · exact .inl ⟨ho,hc.ordinary_component_normal K ho,
      hc.ordinary_component_contains_original K ho,
      (hc.ordinary_module_placement K ho).1.trans inf_le_right,
      D.sourceOrbit_mathieu_pushingUp_ordinary_janko h hmany hV hm hnon hw K ho⟩
  · exact .inr ⟨hfK,hc.constrained_source_input K hK hq hout hfK,
      ChapterC.C27Source.star_model_from_source (hc.constrained_source_input K hK hq hout hfK)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule


open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The original nonfaithful Hall subgroup yields either the refined residual
pushing-up configuration or the full J₄ component of its odd normalizer.
The former has an actual escaping component, and its ordinary case is J₄;
the constrained case retains the original C.2.7 input and star model. -/
theorem sourceOrbit_mathieu_hall_pushingUp_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (MathieuPushingUpComponentCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout⟩ :=
    @sourceOrbit_nonfaithful_hall_escaping_actor G instG finG T L V D
      h hmany hV hnon H hH hlarge B hBN hHall hker
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hc := (le_sectionCentralizer_iff A L).mp hAC
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · have hcomp := D.sourceOrbit_mathieu_normal_component_of_unique h.toHypothesis1221 hV hm
      A hne (le_inf hc.1 hAV) hodd hu hout
    have hrows := D.sourceOrbit_mathieu_component_rows h.toHypothesis1221 hV hm
      A hc.1 hc.2 hodd hAV hcomp
    exact .inr ⟨hu,@sourceOrbit_mathieu_janko_component G instG finG T L V D
      h.toHypothesis1221 hm A hc.1 hc.2 hodd hAV hrows⟩
  · exact .inl (D.sourceOrbit_mathieu_pushingUp_component h hmany hV hnon hm
      A hc.1 hc.2 hodd hAV hu)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
