module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCoreContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimePointLiftSource

/-!
# The original covering core inside the factor normalizer

On the same full-action two-factor witnesses, retain the A₄ bound for the
image of T₁ intersect D and the faithful identification of the full kernel
with O₂(D). The index-two Sylow calculation places the actual ambient image
of O₂(D) inside T₁ and proves T_A = T₁ (T_A intersect D).

The original commutator bound with each other factor's literal five-residual
then makes D normalize that residual. The displayed Sylow factorization
makes T_A normalize it as well. No kernel-containment premise is assumed.
The resulting normalizer chain forces the first full factor to normalize
the common eight-group, contradicting its canonical support. Thus the
full-action two-factor branch is excluded. The simultaneous-cubic and
one-factor alternatives remain to be resolved.

Source: Aschbacher–Smith 14.7.6, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components ChapterA.Section04
open Theory.GroupAction.ElementaryEightPointResidual
open scoped IsMulCommutative Pointwise
universe u

/-- The original covering core lies in T₁, and both the component and its
compatible ambient Sylow normalize the actual other-factor five-residuals. -/
theorem local_minimal_five_core_normalizer
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  ∃ D : Subgroup (normalizer (C : Set G)),
                    D.IsCComponent ∧ D.Normal ∧ D.map C.normalizerMonoidHom = ⊤ ∧
                    D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                      normalizer (C : Set G) ∧
                    (Nat.card (smallSupportFactors (HStar I)
                      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                        (∃ x : I, S = (x : G)⁻¹ • T) ∧
                        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                        let DA := D.map (normalizer (C : Set G)).subtype
                        let L0 := D ⊓ (conjugationImage (F.Li L 1) C).comap C.normalizerMonoidHom
                        let L0G := L0.map (normalizer (C : Set G)).subtype
                        ∃ TA : Sylow 2 G,
                          T1 ≤ TA ∧ (TA : Subgroup G) ≤ normalizer (C : Set G) ∧
                          (TA : Subgroup G) ≤ normalizer (L0G : Set G) ∧
                          DA.pCoreIn 2 ≤ T1 ∧
                          T1 ⊔ ((TA : Subgroup G) ⊓ DA) = (TA : Subgroup G) ∧
                          (∀ j : smallSupportFactors (HStar I)
                              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2,
                            i ≠ j →
                            let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                            let K0 := (primeToResidual 5 K2).map K2.subtype
                            actorImage I K0 = j.val ∧ K0.pCoreIn 2 ≠ ⊥ ∧
                            K1 ≤ normalizer (K0 : Set G) ∧
                            normalizer (K0 : Set G) ≤ normalizer (DA : Set G) ∧
                            DA ≤ normalizer (K0 : Set G) ∧
                            (TA : Subgroup G) ≤ normalizer (K0 : Set G)) ∧
                          DA ∈ Chapter1.LStar G (TA : Subgroup G) ∧ IsFaithfulSignalizerType DA ∧
                          (DA.subgroupOf (DA ⊔ (TA : Subgroup G))).Normal ∧
                          (C.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
                          Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) ∧
                          normalizer (C : Set G) ≤ normalizer (DA : Set G) ∧
                          IsMaximalTwoLocal (normalizer (DA : Set G)) ∧
                          (∀ M : Subgroup G, IsMaximalTwoLocal M → DA ⊔ (TA : Subgroup G) ≤ M →
                            M = normalizer (DA : Set G)))) := by
  obtain ⟨I,hIJ,hI,hIne,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
      hbase,hopp,hnepoints,hresult⟩ :=
    local_minimal_five_point_preimage_control h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  refine ⟨I,hIJ,hI,hIne,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
    hbase,hopp,hnepoints,?_⟩
  rcases hresult with hpair | ⟨D,hD,hnD,hmD,hjoin,hfull⟩
  · exact Or.inl hpair
  · refine Or.inr ⟨D,hD,hnD,hmD,hjoin,?_⟩
    intro htwo
    obtain ⟨S,hSI,hBS,hconj,hindex,hT1C,hSyl,hother,hcentral,hcomm,hpointImage,h12,he,
      hL0image,hL0kernel,P,hT1P,hPL0,TA,hTA⟩ := hfull htwo
    have hTAC : (TA : Subgroup G) ≤ normalizer (C : Set G) :=
      hTA.le.trans (map_subtype_le _)
    let := hCE
    let := hnD
    have hfaith := common_eight_component_faithful_normalizer h.source.simpleQTKE T faithful
      C hCc TA hTAC D hD hmD
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
    let DA := D.map (normalizer (C : Set G)).subtype
    have hT1TA : T1 ≤ TA := hT1P.trans hTA.ge
    obtain ⟨hcore,hgen⟩ := common_eight_component_core_containment S TA T1 C
      inf_le_left hindex hT1TA hTAC hCc D hmD hfaith.2.2.2.1
      (conjugationImage (F.Li L 1) C) h12 hpointImage
    refine ⟨S,hSI,hconj,TA,hT1TA,hTAC,hTA.le.trans hPL0,hcore,hgen,?_,hfaith⟩
    intro j hij
    let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    obtain ⟨hT1K0,hmK0,_,_⟩ := hother j hij
    obtain ⟨_,hcK0⟩ := local_other_factor_component_commutator a f i j
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hij hAi hCpre hCE hCc
      h.source.simpleQTKE D hD hmD
    obtain ⟨hDK0,hTAK0⟩ := five_residual_normalized_of_component_core_containment DA T1 K2 TA
      hcore hgen hT1K0 hcK0
    have hneK0 : actorImage I ((primeToResidual 5 K2).map K2.subtype) ≠ ⊥ := by
      rw [hmK0]
      intro hz
      have hc := j.property.2.1
      rw [hz,card_bot] at hc
      norm_num at hc
    have hcoreK0 := local_five_residual_core_ne_bot a (f.factor j) hneK0
    have hK1K0 := local_factor_normalizes_other_five_residual a f i j hij
    have hNK0 := five_residual_normalizer_le_component_normalizer DA
      ((primeToResidual 5 K2).map K2.subtype) TA hcoreK0 hDK0 hTAK0 hfaith.2.2.2.2.2.2.2
    exact ⟨hmK0,hcoreK0,hK1K0,hNK0,hDK0,hTAK0⟩

/-- The original two-factor alternative can only have simultaneous cubic
endpoint actions: the full common-space action gives a contradiction. -/
theorem local_minimal_five_two_factor_exclusion
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  Nat.card (smallSupportFactors (HStar I)
                    (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≠ 2) := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,hr⟩ :=
    local_minimal_five_core_normalizer h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  refine ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,?_⟩
  rcases hr with hpair | ⟨D,hD,hnD,hmD,hjoin,hfull⟩
  · exact Or.inl hpair
  · right
    intro htwo
    obtain ⟨S,hSI,hconj,TA,hT1TA,hTAC,hTAL0,hcore,hgen,hother,hrest⟩ := hfull htwo
    obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    have hK1D : K1 ≤ normalizer (D.map (normalizer (C : Set G)).subtype : Set G) :=
      (hother j hji.symm).2.2.1.trans (hother j hji.symm).2.2.2.1
    have hK1Z : K1 ≤ normalizer (F.Vi 1 : Set G) := (map_subtype_le _).trans hI.2.1
    have hZne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hc := hf.point_card
      change Nat.card (F.Vi 1) = 2 at hc
      rw [hz,card_bot] at hc
      omega
    let := hCE
    have hK1C := (le_inf hK1Z hK1D).trans
      (normalizes_common_space_of_normalizes_point_cover C (F.Vi 1) hbase hZne D hmD)
    exact local_factor_not_normalizes_common a f i
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hAi hAc hpre hCE hCc hK1C

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
