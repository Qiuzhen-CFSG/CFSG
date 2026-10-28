module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.OddModelResidue
public import CFSG.Quasithin.ChapterI.Section03.MathieuComponentEquality

/-!
# Resolving the original cubic residual or detecting a large odd core

The original central cubic and fixed M₂₂ cover resolve all quotient-model
alternatives once the odd prime cores of its full centralizer have small
rank. The residual then equals its original odd-E orbit and is a normal
ordinary component. Commutators of the selected involution with cubic-fixing
elements centralize that same residual.

The unconditional Hall application retains a precise alternative: an actual
odd prime core of rank at least three in the cubic centralizer, whose
two-rank is consequently at most three. Eliminating this rank obstruction,
the pushing-up commutator contradiction, and the separate M₂₄ fixed-line
and odd-actor comparisons remain necessary for Hall faithfulness.

All full covering groups, placed elements, quotient maps and Hall hypotheses
are retained. Source: Aschbacher--Smith 4.2.13, printed p.612, and
4.4.14, printed pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape

/-- Resolve the same cubic residual as an ordinary normal component, or exhibit
an odd prime core of rank at least three in its full centralizer. -/
@[expose] def CubicPumpupResolution {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  let S := cubicResidualImage H K x
  let Cx := centralizer ({((x : H) : G)} : Set G)
  (S.subgroupOf Cx = componentOrbit (S.subgroupOf Cx) (oddELayer Cx) ∧
    IsComponentIn S Cx ∧ (S.subgroupOf Cx).Normal ∧
    ⁅zpowers r, Cx⁆ ≤ centralizer (S : Set G)) ∨
  (primeRank 2 Cx ≤ 3 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 < primeRank p (pCore p Cx))

private theorem simultaneous_component_restrict
    {G : Type*} [Group G] (x r : G) (hrx : r ∈ centralizer ({x} : Set G))
    (S : Subgroup G)
    (hS : IsComponentIn S (centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G))) :
    IsComponentIn (S.subgroupOf (centralizer ({x} : Set G)))
      (centralizer ({(⟨r,hrx⟩ : centralizer ({x} : Set G))} : Set (centralizer ({x} : Set G)))) := by
  let Cx := centralizer ({x} : Set G)
  let C := centralizer ({(⟨r,hrx⟩ : Cx)} : Set Cx)
  let Cr := centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)
  let D := S.subgroupOf Cx
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  have hDC : D ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hS.1 hs).2))
  let f : C →* Cr := (Cx.subtype.comp C.subtype).codRestrict Cr (fun c =>
    ⟨c.val.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property))⟩)
  let e : (D.subgroupOf C) ≃* S :=
    (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hSCx)
  let := hS.quasisimple
  exact ⟨hDC,hS.2.1.comap f,IsQuasisimple.of_mulEquiv e.symm⟩

/-- All model exclusions, including odd G₂ and McL, apply to the full original
component once its odd prime cores have small rank. Failure supplies the exact
rank obstruction rather than an assumed equality or a new model callback. -/
theorem cubic_pumpup_resolution {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (hx : orderOf x = 3)
    (r : G) (hr : orderOf r = 2) (hdata : CubicAmbientData H K x)
    (hp : CubicPumpupData H K x r)
    (hS : IsComponentIn (cubicResidualImage H K x)
      (centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)))
    (eS : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* Sporadic.Mathieu.M22) :
    CubicPumpupResolution H K x r := by
  obtain ⟨hrx,hX,hn,hinv,hle,_,_⟩ := hp
  obtain ⟨_,_,hxS,_,hqt,hkg,_⟩ := hdata
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let S := cubicResidualImage H K x
  let D := S.subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  let e : D ≃* solvableResidual (centralizer ({x} : Set K)) :=
    (subgroupOfEquivOfLe hSCx).trans
      (((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
        (centralizer ({x} : Set K)).subtype
        (centralizer ({x} : Set K)).subtype_injective).trans
        (((solvableResidual (centralizer ({x} : Set K))).map
          (centralizer ({x} : Set K)).subtype).equivMapOfInjective
            (H.subtype.comp K.subtype) (H.subtype_injective.comp K.subtype_injective))).symm
  let c : Cx := ⟨((x : H) : G),mem_centralizer_singleton_iff.mpr rfl⟩
  have hc : c ∈ center Cx := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.property))
  have hc3 : orderOf (⟨c,hc⟩ : center Cx) = 3 :=
    (orderOf_coe _).symm.trans ((orderOf_coe c).symm.trans
      ((orderOf_coe (x : H)).trans ((orderOf_coe x).trans hx)))
  have hD := simultaneous_component_restrict _ r hrx S hS
  rcases central_cubic_orbit_eq_or_large_odd_core hqt hkg (⟨r,hrx⟩ : Cx)
    ((orderOf_coe _).symm.trans hr) D hD ((centerQuotientCongr e).trans eS)
    ⟨c,hc⟩ hc3 hxS hX hinv with heq | hbad
  · have hDn : D.Normal := heq.symm ▸ hn
    let := hD.quasisimple
    have hDs : D.IsSubnormal := heq.symm ▸ hX.1.subnormal
    have hDc : IsComponentIn S Cx := ⟨hSCx,hDs,inferInstance⟩
    have hXN : Cx ≤ normalizer (S : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hSCx).mp hDn
    have hz : zpowers r ≤ centralizer (S : Set G) := by
      apply zpowers_le.mpr
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hS.1 hy).2
    exact Or.inl ⟨heq,hDc,hDn,(commutator_mono hz le_rfl).trans
      ((le_normalizer_iff_commutator_le_left).mp
        (hXN.trans (normalizer_le_normalizer_centralizer S)))⟩
  · exact Or.inr hbad

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Janko4.InvolutionCentralizers

/-- The original full source configuration with residual equality or a specific large odd core.
The original residual, full covering component and all quotient maps are retained. -/
@[expose] def MathieuPushingUpResolvedCubicCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupResolution H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Resolve the same containing two-component, placed cubic and reselected
involution, or exhibit an odd prime core of rank at least three. -/
theorem pushingUp_cubic_resolution {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpQuotientActionCase L V A) :
    MathieuPushingUpResolvedCubicCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,huy⟩,hux⟩ := hc
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  have hm := cubic_pumpup_resolution H K (g * (x : K) * g⁻¹) hy (r : G)
    ((orderOf_coe r).trans hr) hdata hp hs.1 hey.some
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hm,huy⟩,hux⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction gives full residual equality or a specific
large odd core in the original cubic centralizer. The full cover, quotient maps and all original
Hall hypotheses are retained; no model-exclusion premise is added. -/
theorem sourceOrbit_mathieu_hall_resolved_cubic_obstruction
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
      (MathieuPushingUpResolvedCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_quotient_action_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (@pushingUp_cubic_resolution G instG finG L V A) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
