module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuotientWitness
public import Theory.SpecificGroups.PSL2.QuinticCoreQuotientFusion
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original odd linear-two terminal for a supplied invariant subgroup

The final fusion paragraph of6.1.4 applies to every original subgroup K
containing the quintic residual, normalized by T, outside M, and with actual
K/O₂(K) an odd linear-two group. It does not require K to be a component
of M₁: the preceding odd ternary reduction replaces that component by a
rank-one subgroup. The full original quotient kernel and whole elementary
witness are preserved in the same simultaneous fusion contradiction.

Source: Aschbacher--Smith6.1.4, final paragraph, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V K : Subgroup G} {n : ℕ}

/-- No original T-invariant overgroup of the quintic residual outside M
has an odd prime or quadratic PSL₂ quotient by its full two-core. -/
theorem original_hermitian_no_odd_linear_subgroup
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hXK : quinticResidual T L ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hnot : ¬ K ≤ M)
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hlarge : 3 < p^d) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p^d) := by
  intro hmodel
  let : Fact p.Prime := ⟨hp⟩
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
