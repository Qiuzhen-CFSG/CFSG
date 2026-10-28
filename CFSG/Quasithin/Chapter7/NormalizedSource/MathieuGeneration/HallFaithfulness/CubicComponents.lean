module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicResidual
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.Contained
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

/-!
# The component containing the cubic M₂₂ seed

The marked order-three element belongs to the simultaneous-centralizer
residual on the original full J₄ covering component. Its quasisimple M₂₂
quotient has three-rank two, so the source component theorem places this
seed in a unique normal C-component of the full cubic centralizer. The
central cubic survives that component's two-core quotient, and A.3.6
restricts the quotient to the actual three-cover models.

The literal Hall obstruction constructs this component without an extra
premise. This is a placement and model restriction: identifying the full
cubic residual, placing the cubic in the original intersection residual,
and proving the original pushing-up uniqueness still require arguments.
The involution-centralizer comparison in the other branch is retained.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612; A.3.6 and 1.2.1;
the Hall application is 4.4.14, printed pp.624--625.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section02.RankOneReciprocalEscape

/-- An embedded M₂₂ cover lies in a unique normal C-component of an SQTK group. -/
theorem quasisimple_seed_component {U S : Type*} [Group U] [Finite U]
    [Group S] [Finite S] [IsQuasisimple S]
    (hU : IsSQTK KnownSimple.IsKnownSimple U)
    (e : (S ⧸ center S) ≃* Sporadic.Mathieu.M22)
    (f : S →* U) (hf : Function.Injective f) :
    ∃! Q : Subgroup U, Q.IsCComponent ∧ f.range ≤ Q ∧ Q.Normal ∧
      IsQuasisimple (Q ⧸ pCore 2 Q) := by
  let B := f.range
  let b : S ≃* B := MonoidHom.ofInjective hf
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv b
  have hB : (⊤ : Subgroup B).IsCComponent :=
    (show IsComponent B ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hz : solvableRadical B = center B := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center B) inferInstance inferInstance)
  let q : (B ⧸ solvableRadical B) ≃* Sporadic.Mathieu.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans ((centerQuotientCongr b.symm).trans e)
  have hr : 2 ≤ primeRank 3 (B ⧸ solvableRadical B) := by
    rw [primeRank_equiv 3 q, Sporadic.Mathieu.m22_primeRank_three]
  exact Chapter1.Section02.radical_rank_component_source hU B hB hr

private theorem threeCover_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hm : Chapter1.Section02.LocalModels.ThreeCoverModel X) :
    Chapter1.Section02.LocalModels.ThreeCoverModel Y := by
  open Chapter1.Section02.LocalModels in
    cases hm with
    | classical b q hq he =>
      refine .classical b q hq ?_
      cases b
      · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := he
        exact ⟨F,hF,hfin,hcard,⟨e.symm.trans a⟩⟩
      · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := he
        exact ⟨F,hF,hfin,J,hcard,hconj,⟨e.symm.trans a⟩⟩
    | alternating_six he =>
      obtain ⟨hq,⟨hc⟩,⟨hs⟩⟩ := he
      let := hq
      exact .alternating_six ⟨IsQuasisimple.of_mulEquiv e,
        ⟨(centerCongr e).symm.trans hc⟩,⟨(centerQuotientCongr e.symm).trans hs⟩⟩
    | alternating_seven he =>
      obtain ⟨hq,⟨hc⟩,⟨hs⟩⟩ := he
      let := hq
      exact .alternating_seven ⟨IsQuasisimple.of_mulEquiv e,
        ⟨(centerCongr e).symm.trans hc⟩,⟨(centerQuotientCongr e.symm).trans hs⟩⟩
    | mathieu he =>
      obtain ⟨hq,⟨hc⟩,⟨hs⟩⟩ := he
      let := hq
      exact .mathieu ⟨IsQuasisimple.of_mulEquiv e,
        ⟨(centerCongr e).symm.trans hc⟩,⟨(centerQuotientCongr e.symm).trans hs⟩⟩

/-- A central cubic in a two-core-free quasisimple SQTK group forces a three-cover model. -/
theorem threeCover_of_cubic_center {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (h2 : pCore 2 X = ⊥) (c : center X) (hc : orderOf c = 3) :
    Chapter1.Section02.LocalModels.ThreeCoverModel X := by
  let B := (⊤ : Subgroup X)
  let e : B ≃* X := topEquiv
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  have hB : B.IsCComponent :=
    (show IsComponent X B from ⟨.top,inferInstance⟩).isCComponent
  have hf : generalizedFitting B ≠ fittingSubgroup B := by
    intro he
    have htop : (⊤ : Subgroup B) ≤ generalizedFitting B :=
      component_le_generalizedFitting B ⊤ ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩
    rw [he] at htop
    have hz : center B = ⊤ := top_unique (htop.trans
      ((le_solvableRadical (fittingSubgroup B) inferInstance inferInstance).trans
        IsQuasisimple.solvableRadical_le_center))
    exact Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
    (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))
  obtain ⟨ha,_⟩ := hA36 X hX h2 B hB
  cases ha with
  | simple _ hs _ =>
    let := hs
    have hz : center B = ⊥ := by
      rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with he | he
      · exact he
      · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp he)).elim
    let c' : center B := (centerCongr e).symm c
    have hc' : orderOf c' = 3 := ((centerCongr e).symm.orderOf_eq c).trans hc
    have h1 : c' = 1 := Subtype.ext (mem_bot.mp (hz ▸ c'.property))
    rw [h1,orderOf_one] at hc'
    omega
  | cover _ _ hm => exact threeCover_transport e hm
  | natural ha => exact (hf ha.1).elim
  | nilpotent ha => exact (hf ha.1).elim

open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- Place the full cubic seed in the full centralizer in the original component. -/
theorem pushingUp_cubic_component {G : Type*} [Group G] [Finite G]
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (e : (K ⧸ center K) ≃* Janko4.Model) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
    ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
      (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set R)) ∈
        solvableResidual (centralizer ({x} : Set R)) ∧
      IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
      Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
        center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22) ∧
      ∃! Q : Subgroup (centralizer ({(x : K)} : Set K)),
        Q.IsCComponent ∧
        (solvableResidual (centralizer ({x} : Set R))).map
          (R.subtype.elementCentralizerMap x) ≤ Q ∧ Q.Normal ∧
        IsQuasisimple (Q ⧸ pCore 2 Q) ∧
        (∃ c : center (Q ⧸ pCore 2 Q), orderOf c = 3) ∧
        Chapter1.Section02.LocalModels.ThreeCoverModel (Q ⧸ pCore 2 Q) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
  let := hn
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨x,hx,hqx,hres,hs,⟨es⟩⟩ :=
    Janko4.InvolutionCentralizers.First.CubicResidual.exists_cubic_residual_containing_lift_of_central_cover
      q (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
      (hk.symm ▸ pushingUp_component_center_three_coprime hw K)
  let S := solvableResidual (centralizer ({x} : Set R))
  let := hs
  let f := (R.subtype.elementCentralizerMap x).comp S.subtype
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun y : centralizer ({(x : K)} : Set K) => (y : K)) hab)))
  have hC : IsSQTK KnownSimple.IsKnownSimple (centralizer ({(x : K)} : Set K)) :=
    (hw.2.2.2.2.2.2.1.sqtk.subgroup K).subgroup _
  have hq := quasisimple_seed_component hC es f hf
  have hfr : f.range = S.map (R.subtype.elementCentralizerMap x) := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact mem_map_of_mem _ z.property
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  obtain ⟨Q,⟨hQ,hSQ0,hQn,hQq⟩,hu⟩ := hq
  have hSQ : S.map (R.subtype.elementCentralizerMap x) ≤ Q := hfr.ge.trans hSQ0
  let C := centralizer ({(x : K)} : Set K)
  let cx : C := ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
  have hcx : cx ∈ Q := hSQ
    (mem_map_of_mem (R.subtype.elementCentralizerMap x) hres)
  let c : Q := ⟨cx,hcx⟩
  have hc : orderOf c = 3 := by
    rw [←orderOf_coe c,←orderOf_coe cx]
    exact (orderOf_coe x).trans hx
  have hcc : c ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.val.property
  let π := QuotientGroup.mk' (pCore 2 Q)
  have hπc : π c ∈ center (Q ⧸ pCore 2 Q) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Q) y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcc y)
  have hcop : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Q)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hc)
  have hi := injective_comp_subtype_of_coprime_ker π hcop (zpowers c) hp
  have hπo : orderOf (π c) = 3 :=
    (orderOf_injective (π.comp (zpowers c).subtype) hi ⟨c,mem_zpowers c⟩).trans
      ((orderOf_coe (⟨c,mem_zpowers c⟩ : zpowers c)).symm.trans hc)
  refine ⟨x,hx,hqx,hres,hs,⟨es⟩,Q,⟨hQ,hSQ,hQn,hQq,?_⟩,?_⟩
  · have hc3 : orderOf (⟨π c,hπc⟩ : center (Q ⧸ pCore 2 Q)) = 3 :=
      (orderOf_coe _).symm.trans hπo
    refine ⟨⟨⟨π c,hπc⟩,hc3⟩,?_⟩
    let := hQq
    have hsQ := hC.subgroup Q
    have hQsq : IsSQTK KnownSimple.IsKnownSimple (Q ⧸ pCore 2 Q) := by
      refine ⟨?_,hsQ.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hsQ.stronglyQuasithin p hp ho)
    exact threeCover_of_cubic_center hQsq (pCore_quotient_pCore_eq_bot 2) _ hc3
  · intro Q' hQ'
    exact hu Q' ⟨hQ'.1,hfr.le.trans hQ'.2.1,hQ'.2.2.1,hQ'.2.2.2.1⟩

/-- The original witnesses, with the cubic seed placed in a unique normal
C-component of its full centralizer; its two-core quotient is a three-cover. -/
@[expose] def MathieuPushingUpCubicComponentCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set R)) ∈
            solvableResidual (centralizer ({x} : Set R)) ∧
          IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
          Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
            center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22) ∧
          ∃! Q : Subgroup (centralizer ({(x : K)} : Set K)),
            Q.IsCComponent ∧
            (solvableResidual (centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ≤ Q ∧ Q.Normal ∧
            IsQuasisimple (Q ⧸ pCore 2 Q) ∧
            (∃ c : center (Q ⧸ pCore 2 Q), orderOf c = 3) ∧
            Chapter1.Section02.LocalModels.ThreeCoverModel (Q ⧸ pCore 2 Q)

/-- Construct the full-centralizer component on the same ordinary component,
retaining its ambient witnesses and relative centralizer factorization. -/
theorem mathieu_pushingUp_cubic_component {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (h : MathieuPushingUpJankoInnerCase L V A) :
    MathieuPushingUpCubicComponentCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩,hprod⟩ := h
  exact ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,hprod,e,pushingUp_cubic_component hw K hn e⟩


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction supplies the cubic residual, its unique
normal containing component in the full cubic centralizer, and a three-cover
model for that component’s two-core quotient. The second branch retains the previous involution,
residual-generation seeds and ambient M₂₂ component, unchanged. Neither
remaining source exclusion is assumed or claimed here. -/
theorem sourceOrbit_mathieu_hall_cubic_component_obstruction
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
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpCubicComponentCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_seed_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp mathieu_pushingUp_cubic_component id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
