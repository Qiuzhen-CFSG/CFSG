module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicReplacementCover
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCore

/-!
# Full seed-core placement in the exceptional cubic comparison

The first native J₄ involution-centralizer residual moves its entire two-core.
Lift that identity through the original odd central covering kernel. A
quasisimple image centralizes its normal two-core image, so full movement
forces that image to vanish.

The original seed image is the full cubic fixed residual and is quasisimple.
Applying the native calculation to its literal inclusion and simple-section
projection therefore places the seed's entire two-core in the containing
component's two-core. The other original involution-centralizer model remains
an explicit alternative. All covering components, original residual maps,
replacement witnesses and inclusion-induced quotient markings are retained.

This supplies core placement for the first row in the exceptional comparison.
Original T-normalization, the M₁₂/M₂₂ pushing-up exclusions, and the final
fixed-line and seed-generation comparisons remain open; no Hall-faithfulness
conclusion is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, applied in 4.4.14, printed pp.624--625. The native J₄
certificates retain their imported ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (a : JankoNormalizerAction K)

include a in
/-- The original involution centralizer has central odd core, using the
representative formula for its actual J₄ quotient map. -/
theorem involution_oddCore_central (z : K) (hz : orderOf z = 2) :
    pPrimeCore 2 (centralizer ({z} : Set K)) ≤
      center (centralizer ({z} : Set K)) := by
  obtain ⟨e,he,_⟩ := a.involution_centralizer_quotient z hz
  intro x hx
  have hqx : a.projection ((x : K) : G) = 1 := by
    have hxq : QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set K))) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [←he x,hxq,map_one]
    rfl
  have hzK : (x : K) ∈ center K := by
    have hxq : QuotientGroup.mk' (center K) (x : K) = 1 := by
      apply a.quotientEquiv.injective
      simpa only [map_one] using (a.on_component (x : K)).symm.trans hqx
    exact (QuotientGroup.eq_one_iff (x : K)).mp hxq
  exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hzK y))

include a in
/-- In the first native row, every quasisimple image of the original
full residual kills its entire two-core. -/
theorem involution_residual_first_core_killed
    (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸
      pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
        Janko4.InvolutionCentralizers.First.centralizer)
    {Y : Type*} [Group Y] [IsQuasisimple Y]
    (f : solvableResidual (centralizer ({z} : Set K)) →* Y)
    (hf : Function.Surjective f) :
    pCore 2 (solvableResidual (centralizer ({z} : Set K))) ≤ f.ker := by
  let C := centralizer ({z} : Set K)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 C))
  have hk : q.ker = pPrimeCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact Janko4.InvolutionCentralizers.First.residual_cover_quasisimple_image_kills_twoCore
    q (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [hk]; exact a.involution_oddCore_central z hz)
    (by rw [hk]; exact pPrimeCore_coprime_card) f hf
end JankoNormalizerAction

private theorem core_image_le_of_projection_killed
    {P Q : Type*} [Group P] [Group Q] [Finite Q] (i : P →* Q)
    (hk : pCore 2 P ≤ ((Chapter4.Section04.OddLocalMathieu.projection Q).comp i).ker) :
    (pCore 2 P).map i ≤ pCore 2 Q := by
  let q := QuotientGroup.mk' (pCore 2 Q)
  let U := (pCore 2 P).map (q.comp i)
  have hz : U ≤ center (Q ⧸ pCore 2 Q) := by
    rintro _ ⟨p,hp,rfl⟩
    exact (QuotientGroup.eq_one_iff (q (i p))).mp (hk hp)
  have hn : U.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hz hn) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hn⟩
  have hc : U ≤ pCore 2 (Q ⧸ pCore 2 Q) :=
    le_sSup ⟨hn,pCore_isPGroup.map (q.comp i)⟩
  rw [pCore_quotient_pCore_eq_bot] at hc
  rintro _ ⟨p,hp,rfl⟩
  exact (QuotientGroup.eq_one_iff (i p)).mp
    (mem_bot.mp (hc (mem_map_of_mem (q.comp i) hp)))

/-- Apply the native full-core calculation to the literal source seed and
its given inclusion into the original ambient component's simple section. -/
theorem original_cubic_seed_core_killed_or_second
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) (a : JankoNormalizerAction K)
    (z : K) (hz : orderOf z = 2)
    (P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G) : Subgroup G))
    (hPm : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype))
    {Y : Type*} [Group Y] (f : P →* Y) [IsQuasisimple f.range] :
    pCore 2 P ≤ f.ker ∨
      Nonempty ((centralizer ({z} : Set K) ⧸
        pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
          Janko4.InvolutionCentralizers.Second.ambientCentralizer) := by
  rcases a.involution_centralizer_models z hz with hfirst | hsecond
  · left
    let C := centralizer ({z} : Set K)
    let E := centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G)
    let j := (normalizer (A : Set G)).subtype.comp K.subtype
    let i := j.comp C.subtype
    have hi : Function.Injective i :=
      ((normalizer (A : Set G)).subtype_injective.comp K.subtype_injective).comp
        C.subtype_injective
    have hm : (solvableResidual C).map i = P.map E.subtype := by
      rw [←map_map]
      exact hPm.symm
    let e : solvableResidual C ≃* P :=
      ((solvableResidual C).equivMapOfInjective i hi).trans
        ((MulEquiv.subgroupCongr hm).trans
          (P.equivMapOfInjective E.subtype E.subtype_injective).symm)
    have hk := a.involution_residual_first_core_killed z hz hfirst.some
      (f.rangeRestrict.comp e.toMonoidHom) (f.rangeRestrict_surjective.comp e.surjective)
    intro p hp
    have hecore : e.symm p ∈ pCore 2 (solvableResidual C) := by
      have hm := mem_map_of_mem e.symm.toMonoidHom hp
      rwa [pCore_map_iso 2 e.symm] at hm
    have hh := congrArg f.range.subtype (hk hecore)
    change f (e (e.symm p)) = 1 at hh
    rwa [e.apply_symm_apply] at hh
  · exact Or.inr hsecond

private theorem cubic_seed_image_quasisimple
    {S : Type*} [Group S] [Finite S]
    (hS : IsSQTK KnownSimple.IsKnownSimple S)
    (e : S ≃* Janko4.Model) (b : MulAut S)
    (U : Subgroup S)
    (hU : U = (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype)
    (y : center U) (hy : orderOf y = 3)
    (he : MulAut.conj ((y : U) : S) = b) : IsQuasisimple U := by
  let v : S := y.val.val
  have hv : orderOf (e v) = 3 := by
    rw [e.orderOf_eq]
    exact (orderOf_coe y.val).trans ((orderOf_coe y).trans hy)
  have hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
    refine ⟨?_,?_⟩
    · intro p hp ho
      rw [←primeRank_equiv p e]
      exact hS.stronglyQuasithin p hp ho
    · intro Y _ hY W g hg
      let := hY
      let W' := W.comap e.toMonoidHom
      let r := g.comp (e.toMonoidHom.subgroupComap W)
      have hr : Function.Surjective r := hg.comp
        (e.toMonoidHom.subgroupComap_surjective_of_surjective W e.surjective)
      let a := QuotientGroup.quotientKerEquivOfSurjective r hr
      let : IsSimpleGroup (W' ⧸ r.ker) := a.isSimpleGroup
      exact (hS.isKGroup (W' ⧸ r.ker) inferInstance W' (QuotientGroup.mk' r.ker)
        (QuotientGroup.mk'_surjective _)).of_mulEquiv a.symm
  have hqs := (janko_cubic_residual_at hJ (e v) hv).1
  let := hqs
  have hm : b.fixedSubgroup.map e.toMonoidHom = centralizer ({e v} : Set Janko4.Model) := by
    rw [←he,MulAut.fixedSubgroup_conj,map_centralizer_equiv,Set.image_singleton]
  let c := (e.subgroupMap b.fixedSubgroup).trans (MulEquiv.subgroupCongr hm)
  let r := c.solvableResidualEquiv.symm
  let d := ((solvableResidual b.fixedSubgroup).equivMapOfInjective
    b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective).trans
      (MulEquiv.subgroupCongr hU.symm)
  exact IsQuasisimple.of_mulEquiv (r.trans d)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The full replacement witnesses, with the original seed's entire two-core
placed in the containing component's two-core, or its original involution centralizer
identified as the second native row. -/
@[expose] def MathieuJankoCubicCoveredCoreCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃ Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
              ∃ hn : Q.Normal, letI := hn
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              Nonempty (OddLocalMathieu.SimpleSection Q ≃* Janko4.Model) ∧
              ∃ hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                ∃ x : A, orderOf (OddLocalMathieu.simpleAction Q ⟨x,hAz x.property⟩) = 3 ∧
                  Nat.card ((OddLocalMathieu.simpleAction Q).comp (inclusion hAz)).range = 3 ∧
                  (let f := (OddLocalMathieu.projection Q).comp
                      (OddLocalMathieu.seedInclusion inf_le_left hPQ)
                   let b := (OddLocalMathieu.simpleAction Q).comp (inclusion hAz)
                   f.range = (solvableResidual (b x).fixedSubgroup).map
                     (b x).fixedSubgroup.subtype ∧
                   ∃ y : center f.range, orderOf y = 3 ∧
                     MulAut.conj ((y : f.range) : OddLocalMathieu.SimpleSection Q) = b x ∧
                     b.range = (zpowers ((y : f.range) : OddLocalMathieu.SimpleSection Q)).map
                       MulAut.conj) ∧
                  (((pCore 2 P).map (OddLocalMathieu.seedInclusion inf_le_left hPQ) ≤
                      pCore 2 Q) ∨
                    Nonempty ((centralizer ({z} : Set K) ⧸
                      pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
                        Janko4.InvolutionCentralizers.Second.ambientCentralizer)) ∧
                  ∃ I : Subgroup G,
                    ∃ hPI : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
                      centralizer (A : Set G)).subtype ≤ I,
                    ((I : Set G) =
                      (((solvableResidual (centralizer ({z} : Set K))).map
                        (centralizer ({z} : Set K)).subtype).map
                          ((normalizer (A : Set G)).subtype.comp K.subtype) : Set G) *
                        (I.pCoreIn 2 : Set G)) ∧
                    (∃ e : (P ⧸ pCore 2 P) ≃* (I ⧸ pCore 2 I),
                      ∀ p : P, e (QuotientGroup.mk' (pCore 2 P) p) =
                        QuotientGroup.mk' (pCore 2 I)
                          ⟨(p.val : G),hPI (mem_map_of_mem _ p.property)⟩) ∧
                    I ≤ Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                    A ≤ sectionCentralizer I ∧ Group.IsPerfect I ∧
                    IsQuasisimple (I ⧸ pCore 2 I) ∧
                    Nonempty ((I ⧸ solvableRadical I) ≃* M22) ∧
                    ∃ R : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
                      I = R.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                      R ≤ Q ∧ ∃ (e : OddLocalMathieu.SimpleSection Q ≃* Janko4.Model)
                        (t : Janko4.Model), orderOf t = 2 ∧
                        (∀ c : centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                          MulAut.congr e (OddLocalMathieu.simpleAction Q c) t = t →
                            (c : G) ∈ normalizer (I : Set G)) ∧
                        (R.subgroupOf Q).map (e.toMonoidHom.comp (OddLocalMathieu.projection Q)) =
                          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
                            (centralizer ({t} : Set Janko4.Model)).subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}

/-- Apply full-core movement on the same original seed and retain both
covering components, the replacement and the inclusion-induced quotient map. -/
theorem mathieu_janko_cubic_covered_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : MathieuJankoCubicCoveredReplacementCase (T : Subgroup G) L V A) :
    MathieuJankoCubicCoveredCoreCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,htail⟩ := hc
  let := hnQ
  let := hqs
  let zG : G := ((z : normalizer (A : Set G)) : G)
  let C := centralizer ({zG} : Set G)
  have hzG : orderOf zG = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hz1 : zG ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers zG,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers zG) = 2^1 by
      rw [Nat.card_zpowers,hzG]; rfl)
  let f := (OddLocalMathieu.projection Q).comp (OddLocalMathieu.seedInclusion inf_le_left hPQ)
  let b := (OddLocalMathieu.simpleAction Q).comp (inclusion hAz)
  obtain ⟨y,hy,he,hbr⟩ := hdata.2
  let : IsQuasisimple f.range := cubic_seed_image_quasisimple
    (simpleSection_sqtk (hC.subgroup Q)) hmodel.some (b x) f.range hdata.1 y hy he
  have hk := original_cubic_seed_core_killed_or_second A K a z hz P hPm f
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,
    ⟨hdata.1,y,hy,he,hbr⟩,
    hk.imp (core_image_le_of_projection_killed
      (OddLocalMathieu.seedInclusion inf_le_left hPQ)) id,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,htail⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction now controls the entire original seed
core in the first native row. The alternative identifies the second row;
all existing full-cover replacement data and quotient markings are retained. -/
theorem sourceOrbit_mathieu_hall_cubic_covered_core
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
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
            (p = 3 ∧ MathieuJankoCubicCoveredCoreCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_covered_replacement G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_covered_core h.toHypothesis1221 ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
