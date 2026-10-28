module

public import Theory.Character.ModularBlock.NormalizerRestriction
public import Theory.Character.ModularBlock.NormalizerPrincipalFactor
public import Theory.Character.ModularBlock.BrauerTransitivity

/-!
# Transport of strict normalizer support

A maximal two-coefficient-support subgroup strictly containing the canonical
copy of Q in its normalizer produces a larger ambient subgroup and a nonzero
central idempotent of augmentation zero under its direct principal Brauer
image. The starting centralizer-algebra idempotent is fixed by the normalizer
and lies under the direct Q-Brauer image; all these hypotheses are retained.

Restrict the embedded normalizer idempotent at the larger support subgroup.
Its nonzero support, idempotence, centrality, and augmentation transport to
the ambient centralizer through the canonical centralizer equivalence.
Brauer transitivity and nested normalizer restriction preserve the ambient
factor identity. Finally, injective subgroup inclusion transfers the strict
order increase. Primitive-factor extraction is left to the campaign wrapper.

Extracted from the proof of strict obstruction growth in
`public/lean-eval/glauberman_zStar`, `Submission/ZStar/BrauerThirdMain.lean`
(revision `c3503435`).
-/

public section
noncomputable section
namespace ModularBlock.BrauerThirdMain
open Subgroup PrincipalBlockConstruction
universe v
attribute [local instance] Fintype.ofFinite

/-- A strictly larger maximal coefficient-support subgroup produces a
strictly larger central augmentation-zero idempotent in the ambient centralizer. -/
theorem exists_larger_directBrauerIdempotent_of_strict_normalizer_support
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (Bc : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hBcIdem : IsIdempotentElem Bc)
    (hBcAug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) Bc = 0)
    (hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc)
    (hBcFixed : ∀ n : Subgroup.normalizer (Q : Set G),
      NormalizerBrauerAction.normalizerConjugate
        (BrauerBlockReduction.principalResidueField d) Q n Bc = Bc)
    (D : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hDMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding
        (BrauerBlockReduction.principalResidueField d) Q Bc) D)
    (hPD : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) < D) :
    ∃ (DG : Subgroup G)
      (g : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (DG : Set G))),
      IsPGroup 2 DG ∧
      g ∈ Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (DG : Set G))) ∧
      IsIdempotentElem g ∧ g ≠ 0 ∧
      groupAlgebraAugmentation (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (DG : Set G)) g = 0 ∧
      g * DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) DG
        (BrauerBlockReduction.reducedPrincipalBlockElement d) = g ∧
      Nat.card Q < Nat.card DG := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  let eG : MonoidAlgebra K G :=
    BrauerBlockReduction.reducedPrincipalBlockElement d
  let eGQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) :=
    DefectSupport.subgroupCentralizerRestriction K Q eG
  let eNQ : MonoidAlgebra K N := E eGQ
  let DG : Subgroup G := D.map N.subtype
  have hPLeD : P ≤ D := le_of_lt hPD
  have hDp : IsPGroup 2 D := hDMax.1.1
  have hDGp : IsPGroup 2 DG := hDp.map N.subtype
  have hC : Subgroup.centralizer (DG : Set G) ≤ N := by
    simpa [DG, P, N] using
      centralizer_map_normalizerSubtype_le_normalizer Q D hPLeD
  let ED := BrauerTransitivity.centralizerMapEquiv N D hC
  let bD : MonoidAlgebra K (Subgroup.centralizer (D : Set N)) :=
    DefectSupport.subgroupCentralizerRestriction K D BN
  let eD : MonoidAlgebra K (Subgroup.centralizer (D : Set N)) :=
    DefectSupport.subgroupCentralizerRestriction K D eNQ
  let gD : MonoidAlgebra K (Subgroup.centralizer (DG : Set G)) :=
    MonoidAlgebra.mapDomainRingEquiv K ED bD
  have hBNcenter : BN ∈ Set.center (MonoidAlgebra K N) := by
    exact NormalizerBrauerAction.normalizerAlgebraEmbedding_mem_center_of_fixed
      Q Bc hBcFixed
  have hBNidem : IsIdempotentElem BN := hBcIdem.map E
  have hBNaug : groupAlgebraAugmentation K N BN = 0 := by
    calc
      groupAlgebraAugmentation K N BN =
          groupAlgebraAugmentation K
            (Subgroup.centralizer (Q : Set G)) Bc := by
              exact NormalizerBrauerAction.augmentation_normalizerAlgebraEmbedding
                Q Bc
      _ = 0 := hBcAug
  have heNQcenter : eNQ ∈ Set.center (MonoidAlgebra K N) := by
    have hprops :=
      NormalizerBrauerAction.embeddedSubgroupRestriction_principalProperties
        d Q hQ
    exact hprops.1
  have hBNfactor : BN * eNQ = BN := by
    change E Bc * E eGQ = E Bc
    rw [← E.map_mul, hBcAmbient]
  have hbDcenter : bD ∈ Set.center
      (MonoidAlgebra K (Subgroup.centralizer (D : Set N))) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
      D BN hBNcenter
  have hbDidem : IsIdempotentElem bD := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
      D hDp BN hBNcenter hBNidem
  have hbDne : bD ≠ 0 := by
    simpa [bD] using
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero BN D).mp
        hDMax.1 |>.2
  have hbDaug : groupAlgebraAugmentation K
      (Subgroup.centralizer (D : Set N)) bD = 0 := by
    rw [show groupAlgebraAugmentation K
          (Subgroup.centralizer (D : Set N)) bD =
        groupAlgebraAugmentation K N BN by
      exact SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
        D hDp BN hBNcenter,
      hBNaug]
  have hbDfactor : bD * eD = bD := by
    calc
      bD * eD = DefectSupport.subgroupCentralizerRestriction K D
          (BN * eNQ) := by
            symm
            exact SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
              D hDp BN eNQ hBNcenter heNQcenter
      _ = bD := by rw [hBNfactor]
  have hgDcenter : gD ∈ Set.center
      (MonoidAlgebra K (Subgroup.centralizer (DG : Set G))) := by
    exact BrauerTransitivity.mapDomainRingEquiv_mem_center ED bD hbDcenter
  have hgDidem : IsIdempotentElem gD :=
    BrauerTransitivity.mapDomainRingEquiv_isIdempotent ED bD hbDidem
  have hgDne : gD ≠ 0 :=
    BrauerTransitivity.mapDomainRingEquiv_ne_zero ED bD hbDne
  have hgDaug : groupAlgebraAugmentation K
      (Subgroup.centralizer (DG : Set G)) gD = 0 := by
    rw [show groupAlgebraAugmentation K
          (Subgroup.centralizer (DG : Set G)) gD =
        groupAlgebraAugmentation K
          (Subgroup.centralizer (D : Set N)) bD by
      simpa [gD, DG, ED] using
        BrauerTransitivity.augmentation_mapDomainRingEquiv ED bD,
      hbDaug]
  have heDtrans : MonoidAlgebra.mapDomainRingEquiv K ED eD =
      DefectSupport.subgroupCentralizerRestriction K DG eG := by
    calc
      MonoidAlgebra.mapDomainRingEquiv K ED eD =
          DefectSupport.subgroupCentralizerRestriction K DG
            (RelativeTransferBrauer.subgroupSubtypeMap K N eNQ) := by
              change
                (MonoidAlgebra.mapDomainRingHom K ED.toMonoidHom) eD =
                  DefectSupport.subgroupCentralizerRestriction K DG
                    ((MonoidAlgebra.mapDomainRingHom K N.subtype) eNQ)
              simpa [ED, eD, DG] using
                (BrauerTransitivity.mapDomain_subgroupRestriction_eq_subgroupRestriction_mapDomain
                  N D hC eNQ)
      _ = DefectSupport.subgroupCentralizerRestriction K DG eG := by
        simpa [eNQ, eGQ, E, N, DG, eG] using
          (subgroupRestriction_normalizerEmbedding_subgroupRestriction_eq
            (R := K) Q D hPLeD eG)
  have hgDfactor : gD * DefectSupport.subgroupCentralizerRestriction K DG eG =
      gD := by
    have hmap := congrArg (MonoidAlgebra.mapDomainRingEquiv K ED) hbDfactor
    rw [map_mul, heDtrans] at hmap
    exact hmap
  have hcardPD : Nat.card P < Nat.card D := by
    have hle : Nat.card P ≤ Nat.card D :=
      Subgroup.card_le_of_le hPLeD
    apply lt_of_le_of_ne hle
    intro hcard
    apply hPD.ne
    exact Subgroup.eq_of_le_of_card_ge hPLeD (le_of_eq hcard.symm)
  have hcardPQ : Nat.card P = Nat.card Q := by
    simpa [P, N] using
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv)
  have hcardDGD : Nat.card DG = Nat.card D := by
    exact Subgroup.card_map_of_injective N.subtype_injective
  refine ⟨DG, gD, hDGp, hgDcenter, hgDidem, hgDne, hgDaug, ?_, ?_⟩
  · simpa [eG, K] using hgDfactor
  · calc
      Nat.card Q = Nat.card P := hcardPQ.symm
      _ < Nat.card D := hcardPD
      _ = Nat.card DG := hcardDGD.symm

end ModularBlock.BrauerThirdMain

