module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.AmbientModels
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedSymplectic

/-!
# Further model exclusions on the original cubic pumpup

The original fixed component covering M₂₂ excludes binary PSL₃, the small
derived rank-two endpoints, and every binary PSp₄ family. The latter uses
inner, field and graph involution normal forms. The surviving models are
three odd Lie families, five binary unitary or exceptional families, and McL.

The actual Hall application keeps the same full J₄ cover, placed cubic,
selected involution and quotient maps. It still leaves the trivial-action
equality, the surviving model exclusions and the two source endgames open.
Source: Aschbacher--Smith 4.2.13, printed p.612, and 4.4.14, pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02 ChapterI.MathieuPumpup
open Chapter4.Section02.RankOneReciprocalEscape

/-- Compare the literal fixed component, including its full central cover,
with the remaining unitary, exceptional, odd and McL rows. -/
theorem m22_fixed_component_theoremB_refined
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (a : MulAut Q) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : (B ⧸ center B) ≃* M22) (hm : IsTheoremBModel Q) :
    RemainingMathieuFixedModel Q := by
  let C := B.map a.fixedSubgroup.subtype
  have hC : IsComponentIn C a.fixedSubgroup := by
    refine ⟨map_subtype_le B, ?_⟩
    have he : C.subgroupOf a.fixedSubgroup = B :=
      comap_map_eq_self_of_injective a.fixedSubgroup.subtype_injective B
    exact he.symm ▸ hB
  let e := B.equivMapOfInjective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective
  have h : HasMathieuFixedComponent Q :=
    ⟨a,ha,C,hC,⟨(centerQuotientCongr e).symm.trans eB⟩⟩
  exact h.fixed_model_rows hm

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02

/-- Proper containment leaves either a trivial quotient action and the actual
M₂₂ quotient, or one of the surviving models for a nontrivial action. -/
theorem m22_pumpup_refined_model_comparison
    {G : Type*} [Group G] [Finite G]
    (t : G) (D X : Subgroup G) (hX : X.IsTwoComponent)
    (hm : IsTheoremBModel (X ⧸ oddTwoCore X))
    (ha : M22PumpupQuotientActionData t D X) :
    D = X ∨ Nonempty ((X ⧸ oddTwoCore X) ≃* M22) ∨
      ChapterI.MathieuPumpup.RemainingMathieuFixedModel (X ⧸ oddTwoCore X) := by
  rcases ha with he | ⟨hn,ha,B,hB,eB,hmap,hE,⟨eE⟩,hcase⟩
  · exact Or.inl he
  let := hn
  let : IsSimpleGroup (X ⧸ oddTwoCore X) := hX.isSimpleGroup_quotient_oddTwoCore
  let := hX.1.perfect
  let : Group.IsPerfect (X ⧸ oddTwoCore X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  rcases hcase with ⟨_,he⟩ | ⟨hb,_⟩
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (m22_fixed_component_theoremB_refined _ hb _ hE eE hm))

/-- The literal original residual, its actual odd-E orbit and the remaining
quotient alternatives. This does not assert equality from a quotient marking. -/
@[expose] def CubicPumpupRefinedModelComparison {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) : Prop :=
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let D := (cubicResidualImage H K x).subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  D = X ∨ Nonempty ((X ⧸ oddTwoCore X) ≃* M22) ∨
    ChapterI.MathieuPumpup.RemainingMathieuFixedModel (X ⧸ oddTwoCore X)

/-- Apply the model exclusions to the same cubic, involution and containing
component already supplied by the source configuration. -/
theorem cubic_pumpup_refined_model_comparison {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G)
    (hp : CubicPumpupData H K x r) (ha : CubicPumpupQuotientAction H K x r) :
    CubicPumpupRefinedModelComparison H K x := by
  obtain ⟨hrx,hX,_,_,_,hm,_⟩ := hp
  obtain ⟨hrx',ha⟩ := ha
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let D := (cubicResidualImage H K x).subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  exact m22_pumpup_refined_model_comparison (G := Cx) (⟨r,hrx'⟩ : Cx) D X hX hm ha
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Janko4.InvolutionCentralizers

/-- The original full source configuration after the additional binary model exclusions.
The original residual, full covering component and all quotient maps are retained. -/
@[expose] def MathieuPushingUpRefinedModelComparisonCase {G : Type*} [Group G] [Finite G]
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
              CubicPumpupRefinedModelComparison H K y ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Exclude the binary linear-three, symplectic-four and small derived rows on the unique containing
two-component of the same placed cubic and reselected involution. -/
theorem pushingUp_cubic_refined_model_comparison {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpQuotientActionCase L V A) :
    MathieuPushingUpRefinedModelComparisonCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,huy⟩,hux⟩ := hc
  have hm := cubic_pumpup_refined_model_comparison H K (g * (x : K) * g⁻¹) (r : G) hp hact
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

/-- The literal Hall obstruction excludes the additional binary models on
the original cubic pumpup. The full cover, quotient maps and all original
Hall hypotheses are retained; no model-exclusion premise is added. -/
theorem sourceOrbit_mathieu_hall_refined_model_comparison_obstruction
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
      (MathieuPushingUpRefinedModelComparisonCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_quotient_action_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (@pushingUp_cubic_refined_model_comparison G instG finG L V A) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
