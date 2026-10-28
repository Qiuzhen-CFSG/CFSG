module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeFaithfulCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimePointLiftSource

/-!
# The original common-space component at its compatible ambient Sylow

Apply the faithful-cover calculation to the same original minimal I,
selected endpoint, canonical dihedral factor, and literal commutator C.
The preceding point-preimage construction supplies the actual ambient
Sylow T_A normalizing both C and the full A₄ preimage L₀. Transport the
original EarlierFaithfulClassification G T along Sylow conjugacy, rather
than assuming it at T_A or identifying T_A with T.

The same D now belongs to L_f*(G,T_A), its full C-action kernel is exactly
O₂(D), and D/O₂(D) is L₃(2). Moreover N_G(C) normalizes D, and N_G(D)
is the unique maximal two-local overgroup of DT_A. These statements keep
the actual ambient subgroup maps and the full preimage defining L₀.

The simultaneous-cubic alternative remains explicit. The containment
O₂(D) ≤ T₁, normalization of the other five-residual, the resulting
ambient contradiction, and the one-factor exclusion remain to be proved.
No vanishing of the original five-core or final recognition input is asserted.
Source: Aschbacher–Smith 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
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

/-- The original two-factor full-action branch has a faithful maximal
component at its actual Sylow T_A, with exact action kernel and normalizer
uniqueness. The independent simultaneous-cubic branch is retained. -/
theorem local_minimal_five_faithful_cover
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
    local_minimal_five_point_preimage h hab structural previous J hJ hne
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
    obtain ⟨S,hSI,hBS,hconj,hindex,hT1C,hSyl,hother,hcentral,hcomm,h12,he,
      hL0image,hL0kernel,P,hT1P,hPL0,TA,hTA⟩ := hfull htwo
    have hTAC : (TA : Subgroup G) ≤ normalizer (C : Set G) :=
      hTA.le.trans (map_subtype_le _)
    let := hCE
    have hfaith := common_eight_component_faithful_normalizer h.source.simpleQTKE T faithful
      C hCc TA hTAC D hD hmD
    exact ⟨S,hSI,hconj,TA,hT1P.trans hTA.ge,hTAC,hTA.le.trans hPL0,hfaith⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
