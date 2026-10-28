module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicSeedInvolution
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualCore

/-!
# Full core placement in both original J₄ centralizer rows

Both native involution-centralizer residuals move their entire two-cores.
The original centralizer maps onto one of these native groups with the
specified odd central kernel. Lifting movement through that map and then
transporting along the original residual inclusion shows that the entire
seed core is moved. Its central image in the cubic fixed residual therefore
vanishes, placing O₂(K_Z) in O₂(L_Z) in both rows.

The Hall application retains the full original components, the replacement
product I_Z = K_Z O₂(I_Z), and the inclusion-induced two-core quotient marking.
Original T-normalization of I_Z, the M₁₂/M₂₂ pushing-up branches, the fixed-line
identification and seed-generation comparison remain obligations of
SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, applied in 4.4.14, printed pp.624--625. Native model data
and certificates retain their imported ATLAS attribution and licenses.
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
/-- Full residual-core movement on the original odd central cover,
for either native involution-centralizer row. -/
theorem involution_residual_core_fully_moved (z : K) (hz : orderOf z = 2) :
    ⁅pCore 2 (solvableResidual (centralizer ({z} : Set K))),
      (⊤ : Subgroup (solvableResidual (centralizer ({z} : Set K))))⁆ =
        pCore 2 (solvableResidual (centralizer ({z} : Set K))) := by
  let C := centralizer ({z} : Set K)
  rcases a.involution_centralizer_models z hz with hrow | hrow
  all_goals
    obtain ⟨e⟩ := hrow
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 C))
    have hk : q.ker = pPrimeCore 2 C := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hq := e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 C))
    have hc : q.ker ≤ center C := by rw [hk]; exact a.involution_oddCore_central z hz
    have ho : Nat.Coprime 2 (Nat.card q.ker) := by rw [hk]; exact pPrimeCore_coprime_card
  · exact Janko4.InvolutionCentralizers.First.residual_cover_core_fully_moved q hq hc ho
  · exact Janko4.InvolutionCentralizers.Second.residual_cover_core_fully_moved q hq hc ho
end JankoNormalizerAction

/-- Transfer full-core movement to the literal original seed, retaining
its equality with the full component involution-centralizer residual. -/
theorem original_seed_core_fully_moved
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
    : ⁅pCore 2 P,(⊤ : Subgroup P)⁆ = pCore 2 P := by
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
  apply (map_injective (f := e.symm.toMonoidHom) e.symm.injective)
  rw [map_commutator,pCore_map_iso 2 e.symm,
    map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
  exact a.involution_residual_core_fully_moved z hz

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

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- Full replacement witnesses with the entire original seed core placed
in the containing component core, in both native rows. -/
@[expose] def MathieuJankoCubicFullCoreCase {G : Type*} [Group G]
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

/-- Apply full-core movement on the same original seed and retain both
covering components, the replacement and the inclusion-induced quotient map. -/
theorem mathieu_janko_cubic_full_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : MathieuJankoCubicCoveredReplacementCase (T : Subgroup G) L V A) :
    MathieuJankoCubicFullCoreCase (T : Subgroup G) L V A := by
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
  have hb := cubic_fixed_seed_core_image_bound
    (simpleSection_sqtk (hC.subgroup Q)) hmodel.some (b x) f hdata.1 y hy he
  have hm := original_seed_core_fully_moved A K a z hz P hPm
  have hk : pCore 2 P ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    conv_lhs => rw [←hm]
    rw [map_commutator,←MonoidHom.range_eq_map]
    exact commutator_eq_bot_iff_le_centralizer.mpr hb.1
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,
    ⟨hdata.1,y,hy,he,hbr⟩,
    core_image_le_of_projection_killed (OddLocalMathieu.seedInclusion inf_le_left hPQ) hk,
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

/-- The literal Hall obstruction places the entire original seed core in
both native rows. The original covers, replacement data and inclusion-induced
quotient markings are retained. -/
theorem sourceOrbit_mathieu_hall_cubic_full_core
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
            (p = 3 ∧ MathieuJankoCubicFullCoreCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_covered_replacement G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_full_core h.toHypothesis1221 ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
