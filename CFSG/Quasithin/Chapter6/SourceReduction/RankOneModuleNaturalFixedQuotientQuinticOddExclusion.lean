module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuotientWitness
public import Theory.SpecificGroups.PSL2.QuinticCoreQuotientFusion
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Excluding the original odd linear-two component row

The original residual lies in K and the full T normalizes K. The marked
quintic Sylow action removes the exceptional central-cover field and
identifies K/O₂(K) itself. Pass through the literal KT/O₂(KT), retaining
its full kernel. The original maximum elementary witness has a nonzero
image in O₂(X*T*); simultaneous component fusion returns that whole image
to T* outside the same core, contradicting the original Thompson bound.

Source: Aschbacher--Smith 6.1.4, final paragraph, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual outside component cannot have an odd prime or quadratic
PSL₂ central quotient: the whole original elementary witness contradicts
component fusion through the full original two-core quotient. -/
theorem original_hermitian_component_not_odd_linear
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    : ¬ ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d) := by
  intro hc
  let : Fact p.Prime := ⟨hp⟩
  have hXK := original_hermitian_quintic_le_odd_linear_component
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  have hTK := original_hermitian_odd_linear_component_normalized_by_sylow
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  obtain ⟨_,hmodel,hlarge,_⟩ := original_hermitian_quintic_odd_linear_actual_quotient
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let X := quinticResidual T L
  let R := X.subgroupOf J
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hXJ : X ≤ J := hXK.trans hKJ
  let P := T.subtype hTJ
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let eb : B ≃* K := subgroupOfEquivOfLe hKJ
  let ebq := QuotientGroup.congr (pCore 2 B) (pCore 2 K) eb (pCore_map_iso 2 eb)
  have hgen : B ⊔ (P : Subgroup J) = ⊤ := by
    change K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup hKJ hTJ,subgroupOf_self]
  have hJB : IsPGroup 2 (J ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (P : Subgroup J) P.isPGroup' hgen
  let er : R ≃* X := subgroupOfEquivOfLe hXJ
  have hRp : IsPPerfect 2 R := (quinticResidual_twoPerfect T L).of_surjective
    er.symm.toMonoidHom er.symm.surjective
  have hRfive : Nat.card (R ⧸ pCore 2 R) = 5 := by
    rw [Nat.card_congr (QuotientGroup.congr (pCore 2 R) (pCore 2 X) er
      (pCore_map_iso 2 er)).toEquiv]
    exact (original_hermitian_quintic_core_quotient h hout hm).2
  have hPR : (P : Subgroup J) ≤ normalizer (R : Set J) := by
    rw [←subgroupOf_normalizer_eq hXJ]
    intro t ht
    exact sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes ht
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := (X ⊔ (T : Subgroup G)).pCoreIn 2
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hRP : R ⊔ (P : Subgroup J) = (X ⊔ (T : Subgroup G)).subgroupOf J :=
    (subgroupOf_sup hXJ hTJ).symm
  have hSq : (S.subgroupOf J).map q =
      ((R.map q) ⊔ (P : Subgroup J).map q).pCoreIn 2 := by
    rw [←Subgroup.map_sup,←map_pCoreIn_of_ker_isPGroup q hqker,hRP,
      pCoreIn_subgroupOf 2 (X ⊔ (T : Subgroup G)) J (sup_le hXJ hTJ)]
  obtain ⟨A,hA,hAne,hAS,hreturn⟩ := original_hermitian_outside_quotient_witness h hout hm hnot
  let := hA.2.1
  let : IsElementaryAbelian 2 (A.subgroupOf J) := IsElementaryAbelian.subgroupOf (hA.1.trans hTJ)
  have hAb : IsElementaryAbelian 2 ((A.subgroupOf J).map q) := IsElementaryAbelian.map q
  have hAS' : (A.subgroupOf J).map q ≤ ((R.map q) ⊔ (P : Subgroup J).map q).pCoreIn 2 :=
    hAS.trans_eq hSq
  obtain ⟨g,_,hgT,hgS⟩ := Theory.PSL2.core_quotient_quintic_whole_fusion B hJB ho hd hF
    (by rw [hF]; exact hlarge) (ebq.trans e) P R (comap_mono hXK) hRp hRfive hPR
    ((A.subgroupOf J).map q) hAb hAne hAS'
  exact hgS ((hreturn g hgT).trans_eq hSq)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
