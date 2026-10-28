module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicElevenCore
public import Theory.Mathieu.M22.QuasithinOddCoreBound

/-!
# The full original cubic residual is a normal component

The small odd-core theorem removes the final eleven-core alternative.
The placed cubic residual therefore equals its original odd-E component
orbit in the whole cubic centralizer, is an ordinary normal component, and
centralizes every commutator of that centralizer with the selected involution.
The same literal Hall obstruction supplies this resolved configuration,
with the full J₄ cover and every original quotient and inclusion retained.

This completes the cubic-component identification step of 4.2.13. The
pushing-up commutator contradiction and the separate M₂₄ fixed-line and
odd-actor comparison remain required for Hall faithfulness.
Source: Aschbacher--Smith 4.2.13, printed p.612, and 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape

/-- The original cubic residual is a normal ordinary component of its full centralizer. -/
@[expose] def CubicPumpupFullResolution {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  let S := cubicResidualImage H K x
  let Cx := centralizer ({((x : H) : G)} : Set G)
  S.subgroupOf Cx = componentOrbit (S.subgroupOf Cx) (oddELayer Cx) ∧
    IsComponentIn S Cx ∧ (S.subgroupOf Cx).Normal ∧
    ⁅zpowers r, Cx⁆ ≤ centralizer (S : Set G)

/-- Resolve the same original residual in the full cubic centralizer, with no odd-core alternative. -/
theorem cubic_pumpup_full_resolution {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (hx : orderOf x = 3)
    (r : G) (hr : orderOf r = 2) (hdata : CubicAmbientData H K x)
    (hp : CubicPumpupData H K x r)
    (hS : IsComponentIn (cubicResidualImage H K x)
      (centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)))
    (eS : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* Sporadic.Mathieu.M22) :
    CubicPumpupFullResolution H K x r := by
  rcases cubic_pumpup_eleven_resolution H K x hx r hr hdata hp hS eS with hgood | hbad
  · exact hgood
  exfalso
  obtain ⟨_,_,_,_,hqt,_,_⟩ := hdata
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let S := cubicResidualImage H K x
  let D := S.subgroupOf Cx
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  let e : D ≃* solvableResidual (centralizer ({x} : Set K)) :=
    (subgroupOfEquivOfLe hSCx).trans
      (((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
        (centralizer ({x} : Set K)).subtype
        (centralizer ({x} : Set K)).subtype_injective).trans
        (((solvableResidual (centralizer ({x} : Set K))).map
          (centralizer ({x} : Set K)).subtype).equivMapOfInjective
            (H.subtype.comp K.subtype) (H.subtype_injective.comp K.subtype_injective))).symm
  let := hS.quasisimple
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hSCx).symm
  exact (not_le_of_gt hbad.2.2) (M22CentralCover.eleven_core_rank_le_two hqt D
    ((centerQuotientCongr e).trans eS))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Janko4.InvolutionCentralizers

/-- The original full source configuration with the cubic residual resolved.
The original residual, full covering component and all quotient maps are retained. -/
@[expose] def MathieuPushingUpNormalCubicCase {G : Type*} [Group G] [Finite G]
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
              CubicPumpupFullResolution H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Resolve the same containing two-component, placed cubic and reselected involution. -/
theorem pushingUp_full_cubic_resolution {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpQuotientActionCase L V A) :
    MathieuPushingUpNormalCubicCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,huy⟩,hux⟩ := hc
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  have hm := cubic_pumpup_full_resolution H K (g * (x : K) * g⁻¹) hy (r : G)
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

/-- The literal Hall obstruction gives full cubic residual equality and normality.
The full cover, original quotient maps and all Hall hypotheses are retained. -/
theorem sourceOrbit_mathieu_hall_normal_cubic_obstruction
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
      (MathieuPushingUpNormalCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_quotient_action_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (@pushingUp_full_cubic_resolution G instG finG L V A) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
