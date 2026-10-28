module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicFullCore
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Janko

/-!
# Excluding the second original centralizer row in the cubic branch

The native odd-primary covering theorem makes the center of the original
J₄ component a two-group. Its specified action has odd kernel and is
faithful on two-subgroups, so this center is trivial. The same original
projection then kills no odd core in its involution centralizer.

In the second native row that centralizer has order 1816657920, whose
three-part is nine. The full cubic fixed seed, however, has an M₂₂ central
quotient and an actual central element of order three, so its order is
divisible by 27. Transport through the literal full residual equality
makes these facts incompatible. The exceptional cubic branch therefore
uses the first native involution centralizer.

The Hall consumer retains the original component, the containing component,
all residual inclusions, full-core placement, the replacement product and
its inclusion-induced quotient isomorphism. Triviality of the first
component's covering center is proved, not assumed; no restriction on the
containing component's covering center is introduced. Original T-normalization
of the replacement, M₁₂/M₂₂ pushing up, fixed-line identification, seed
generation and the separate odd-normalizer assembly remain open.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), I.1.3,
4.4.3 and 4.4.14, printed pp.407,623--625. Imported native matrix and
covering calculations retain their source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (a : JankoNormalizerAction K) [IsQuasisimple K]

include a in
/-- The original component's covering center vanishes: the native covering
bound makes it a two-group, while its original action has odd kernel. -/
theorem component_center_eq_bot : center K = ⊥ := by
  have hp := Janko4.OddPrimary.source_center_isPGroup ⟨a.quotientEquiv⟩
  let Z := (center K).map K.subtype
  have hi := a.injective_on_twoSubgroup Z (hp.map K.subtype)
  apply bot_unique
  intro z hz
  have hzZ : (z : G) ∈ Z := mem_map_of_mem K.subtype hz
  have he : a.projection (z : G) = 1 := by
    have hq : QuotientGroup.mk' (center K) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [a.on_component,hq,map_one]
  have hh : (⟨z,hzZ⟩ : Z) = 1 := hi (he.trans (map_one _).symm)
  exact Subtype.ext (congrArg (fun x : Z => (x : G)) hh)

include a in
/-- The odd kernel in the original involution-centralizer projection vanishes
by the proved triviality of the full component's center. -/
theorem involution_oddCore_eq_bot (z : K) (hz : orderOf z = 2) :
    pPrimeCore 2 (centralizer ({z} : Set K)) = ⊥ := by
  obtain ⟨e,he,_⟩ := a.involution_centralizer_quotient z hz
  apply bot_unique
  intro x hx
  have hp : a.projection ((x : K) : G) = 1 := by
    have hq : QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set K))) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [←he x,hq,map_one]
    rfl
  have hk : (x : K) ∈ center K := by
    have hq : QuotientGroup.mk' (center K) (x : K) = 1 := by
      apply a.quotientEquiv.injective
      simpa only [map_one] using (a.on_component (x : K)).symm.trans hp
    exact (QuotientGroup.eq_one_iff (x : K)).mp hq
  rw [a.component_center_eq_bot] at hk
  exact Subtype.ext (mem_bot.mp hk)

include a in
/-- The second original centralizer has only two factors of three in its order. -/
theorem involution_second_not_twentySeven_dvd (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸
      pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
        Janko4.InvolutionCentralizers.Second.ambientCentralizer) :
    ¬ 27 ∣ Nat.card (centralizer ({z} : Set K)) := by
  let d := (QuotientGroup.quotientMulEquivOfEq (a.involution_oddCore_eq_bot z hz)).trans
    QuotientGroup.quotientBot
  have hc : Nat.card (centralizer ({z} : Set K)) = 1816657920 :=
    (Nat.card_congr (d.symm.trans e).toEquiv).trans
      Janko4.InvolutionCentralizers.Second.ambient_card
  rw [hc]
  decide
end JankoNormalizerAction

open Sporadic.Mathieu in
/-- The whole cubic fixed seed has a central cubic and an M₂₂ central
quotient. Thus its original surjecting group has order divisible by 27. -/
theorem cubic_fixed_seed_twentySeven_dvd
    {S P : Type*} [Group S] [Finite S] [Group P] [Finite P]
    (hS : IsSQTK KnownSimple.IsKnownSimple S)
    (e : S ≃* Janko4.Model) (b : MulAut S) (f : P →* S)
    (hU : f.range = (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype)
    (y : center f.range) (hy : orderOf y = 3)
    (he : MulAut.conj ((y : f.range) : S) = b) :
    27 ∣ Nat.card P := by
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
  obtain ⟨hqs,⟨er⟩,_⟩ := janko_cubic_residual_at hJ (e v) hv
  let C := centralizer ({e v} : Set Janko4.Model)
  have hm : b.fixedSubgroup.map e.toMonoidHom = C := by
    rw [←he,MulAut.fixedSubgroup_conj,map_centralizer_equiv,Set.image_singleton]
  let c := (e.subgroupMap b.fixedSubgroup).trans (MulEquiv.subgroupCongr hm)
  let d := ((solvableResidual b.fixedSubgroup).equivMapOfInjective
    b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective).trans
      (MulEquiv.subgroupCongr hU.symm)
  let a := c.solvableResidualEquiv.symm.trans d
  let ez := QuotientGroup.congr (center (solvableResidual C)) (center f.range) a (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr a ⟨z,hz⟩).property
    · intro z hz
      exact ⟨a.symm z,(centerCongr a.symm ⟨z,hz⟩).property,a.apply_symm_apply z⟩)
  have hq : Nat.card (f.range ⧸ center f.range) = 443520 :=
    (Nat.card_congr (ez.symm.trans er).toEquiv).trans m22_order
  have h3 : 3 ∣ Nat.card (center f.range) := hy ▸ orderOf_dvd_natCard y
  have h27 : 27 ∣ Nat.card f.range := by
    rw [(center f.range).card_eq_card_quotient_mul_card_subgroup,hq]
    exact Nat.mul_dvd_mul (by decide : 9 ∣ 443520) h3
  exact h27.trans (card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective)


/-- The original full seed cannot come from the smaller J₄ centralizer row:
its literal cubic fixed image requires a third factor of three. -/
theorem original_cubic_seed_first_row
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    [IsQuasisimple K] (a : JankoNormalizerAction K)
    (z : K) (hz : orderOf z = 2)
    (P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G) : Subgroup G))
    (hPm : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype))
    (hS : IsSQTK KnownSimple.IsKnownSimple S)
    (e : S ≃* Janko4.Model) (b : MulAut S) (f : P →* S)
    (hU : f.range = (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype)
    (y : center f.range) (hy : orderOf y = 3)
    (he : MulAut.conj ((y : f.range) : S) = b) :
    Nonempty ((centralizer ({z} : Set K) ⧸
      pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
        Janko4.InvolutionCentralizers.First.centralizer) := by
  rcases a.involution_centralizer_models z hz with hfirst | ⟨esecond⟩
  · exact hfirst
  exfalso
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
  let d : solvableResidual C ≃* P :=
    ((solvableResidual C).equivMapOfInjective i hi).trans
      ((MulEquiv.subgroupCongr hm).trans
        (P.equivMapOfInjective E.subtype E.subtype_injective).symm)
  have h27 := cubic_fixed_seed_twentySeven_dvd hS e b f hU y hy he
  rw [←Nat.card_congr d.toEquiv] at h27
  exact a.involution_second_not_twentySeven_dvd z hz esecond.some
    (h27.trans (solvableResidual C).card_subgroup_dvd_card)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The full cubic witnesses with the original component center proved trivial
and its original involution centralizer forced into the first native row. -/
@[expose] def MathieuJankoCubicFirstRowCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧ center K = ⊥ ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        Nonempty ((centralizer ({z} : Set K) ⧸
          pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
            Janko4.InvolutionCentralizers.First.centralizer) ∧
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
                  ((pCore 2 P).map (OddLocalMathieu.seedInclusion inf_le_left hPQ) ≤
                      pCore 2 Q) ∧
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

/-- Exclude the second row on the original full component, preserving the
replacement, both covering components and every original quotient marking. -/
theorem mathieu_janko_cubic_first_row
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : MathieuJankoCubicFullCoreCase (T : Subgroup G) L V A) :
    MathieuJankoCubicFirstRowCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,htail⟩ := hc
  let := hK.2
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
  have hfirst := original_cubic_seed_first_row A K a z hz P hPm
    (simpleSection_sqtk (hC.subgroup Q)) hmodel.some (b x) f hdata.1 y hy he
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,a.component_center_eq_bot,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,
    ⟨hdata.1,y,hy,he,hbr⟩,
    hcore,
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

/-- The literal Hall obstruction forces the first native centralizer row in
the exceptional cubic branch, with the original covering groups, full seed
and inclusion-induced quotient markings retained. -/
theorem sourceOrbit_mathieu_hall_cubic_first_row
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
            (p = 3 ∧ MathieuJankoCubicFirstRowCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_full_core G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_first_row h.toHypothesis1221 ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
