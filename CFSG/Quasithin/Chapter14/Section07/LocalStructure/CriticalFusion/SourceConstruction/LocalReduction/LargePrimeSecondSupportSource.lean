module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSecondSupport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeComponentCoverSource

/-!
# The second-support calculation on the original minimal local witness

Reuse the original selected minimal I, common eight-group C, canonical
factors and covering component. In the full-action two-factor branch the
compatible Sylow S, its index-two factor normalizer T₁ and its Sylow
certificate inside N_I(C) are retained. The same T₁ intersected with the
component fixes the other four-dimensional support and centralizes the
literal point cubic and L₁/O₂(L₁).

The result preserves the simultaneous-cubic branch and assumes no support
or point-centralization conclusion. It prepares the source construction of
L₀ and T_A; neither that construction nor five-core vanishing is asserted.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
universe u
open Chapter14.Section06.OddCriticalPair.Selection
open Theory.GroupAction.ElementaryEightPointResidual
open scoped Pointwise
/-- A narrow application on the original selected witnesses: in the full-action
branch the compatible Sylow intersection fixes the second support and centralizes
the original point residual modulo its own two-core. The cubic branch is retained. -/
theorem local_minimal_five_second_support
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) )
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
                        c.endpoint.conjugate (F.UH I) ≤ S ∧
                        (∃ x : I, S = (x : G)⁻¹ • T) ∧
                        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                        let DA := D.map (normalizer (C : Set G)).subtype
                        T1.relIndex (S : Subgroup G) = 2 ∧ T1 ≤ normalizer (C : Set G) ∧
                        (∃ P : Sylow 2 (I ⊓ normalizer (C : Set G) : Subgroup G),
                          (P : Subgroup (I ⊓ normalizer (C : Set G) : Subgroup G)).map
                            (I ⊓ normalizer (C : Set G)).subtype = T1) ∧
                        (∀ j : smallSupportFactors (HStar I)
                            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2,
                          i ≠ j →
                          let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                          let K0 := (primeToResidual 5 K2).map K2.subtype
                          T1 ≤ normalizer (K0 : Set G) ∧ actorImage I K0 = j.val ∧
                          actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) ∧
                          subspaceCommutator a.representation ⊤ j.val ≤
                            fixedSpace a.representation (actorImage I (T1 ⊓ DA))) ∧
                        actorImage I (T1 ⊓ DA) ≤
                          centralizer (actorImage I (F.Li L 1) : Set (HStar I)) ∧
                        ⁅T1 ⊓ DA,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,
      hr,hAc,hAd,hCX,hW,hcomp,hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,
      r,hlabels,hprod,hrr,hrd,hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,
      hLC,hLZ,hCS,hoppN,hoppZ,hfixed,hfixedOpp,himageB,himageOpp,
      hsupp,hsuppOpp,hindex,hpair,hcubic,hcubicOpp,hresult,hnormalizer⟩ :=
    local_minimal_five_full_cover_or_cubic_pair h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  have hAi : actorImage I (c.endpoint.conjugate (F.UH I)) ≤ f.factor i := by
    rw [hfi]
    exact le_sup_right
  have hCpre : C = Chapter14.Section06.OddNormalizer.supportPreimage a
      (subspaceCommutator a.representation ⊤ (actorImage I (c.endpoint.conjugate (F.UH I)))) := by
    simpa only [himage] using hpre
  have hIne : pCore 5 (HStar I) ≠ ⊥ := by
    intro hz
    rw [hcore,hz,card_bot] at hcard
    omega
  refine ⟨I,hIJ,hI,hIne,hproper,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
    hbase,hopp,hnepoints,?_⟩
  rcases hresult with hpairC | ⟨hfullC,heC,⟨D,hD,hmD,hjoin,hquot,hnD,hker,hmodel,hfree,hother⟩,hpoints⟩
  · exact Or.inl hpairC
  · refine Or.inr ⟨D,hD,hnD,hmD,hjoin,?_⟩
    intro htwo
    obtain ⟨S,hSI,hBS,hconj,hindexT,hindexS,hT1C,hIC,hSyl⟩ := hnormalizer htwo
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
    let DA := D.map (normalizer (C : Set G)).subtype
    have hall := fun j hij => local_other_factor_support_fixed a f i j
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hij htwo hAi hCpre hCE hCc
      h.source.simpleQTKE D hD hmD S hSI
    obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
    have hdimj : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ j.val) = 4 := by
      have hh := j.property.2.2
      rw [BinaryGroupAction.commutator_card] at hh
      exact Nat.pow_right_injective (by decide : 1 < 2) hh
    have hPj : actorImage I (F.Li L 1) ≤ centralizer (j.val : Set (HStar I)) :=
      hPD.trans (centralizer_le ((f.contains j).trans (le_iSup f.factor j)))
    have hc := local_point_centralized_of_other_support_fixed h structural I
      (F.Li_one_le_of_mem_Hz hI) hn a j.val hdimj hPj
      (T1 ⊓ DA) (inf_le_left.trans (inf_le_left.trans hSI)) (hall j hji.symm).2.2.2
    exact ⟨S,hSI,hBS,hconj,hindexS,hT1C,hSyl,hall,hc⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
