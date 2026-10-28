module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeFactorNormalizerSource
public import Theory.GroupAction.ElementaryEightPointResidual.Conjugation

/-!
# The actual residual images at the selected quintic endpoints

The same minimal five-core witness supplies an elementary common commutator
C of order eight. Both original point residuals normalize C and fix exactly
their respective distinct point lines. Their intrinsic two-core quotients
have order three. Applying the literal conjugation-image calculation at
both endpoints gives a cubic image or an actual A₄ isomorphism. The cubic
case is equivalent to centralization of C by that endpoint residual's
original two-core.

All previous witness conditions are retained, including the selected actor,
the canonical dihedral factor, both point lines, the full central preimage,
and the compatible Sylow normalizer. No new recognition premise is assumed.
The remaining task is to exclude the cubic branch using the original
ambient hypotheses, establish the full endpoint normalizer images and
complete both five-core exclusions. In particular 14.5.21(1) pairs
U/C_U(O₂(I)) with its dual; its denominator is not automatically V₁.

Source: Aschbacher–Smith, 14.5.21(1), printed p.1019, and 14.7.6,
printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Theory.GroupAction.ElementaryEightPointResidual
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- Both endpoint residual images on the same selected common three-space,
with the exact remaining cubic obstruction and all normalizer data retained. -/
theorem local_minimal_five_endpoint_images
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X.Normal ∧ IsElementaryAbelian 5 X ∧ X = pCore 5 (HStar I) ∧
      (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      (∀ N : Subgroup (HStar I), N.Normal → N ≤ X → N = ⊥ ∨ N = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
      ⁅F.UH I,F.Li L 1⁆ = F.UH I ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          (∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1) ∧
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            3 ≤ hf.b ∧ Odd hf.b ∧
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              A ≤ centralizer (((F.Li L 1).subgroupOf I).map
                (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) ∧
              A ⊓ centralizer (X : Set (HStar I)) = ⊥ ∧
              rank A = 1 ∧ Nat.card A = 2 ∧ fixedCodim a.representation A = 2 ∧
              Nat.card (⁅X,A⁆ : Subgroup (HStar I)) = 5 ∧
              Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,A⁆) = 4 ∧
              IsCompl (subspaceCommutator a.representation ⊤ ⁅X,A⁆)
                (fixedSpace a.representation (⁅X,A⁆ ⊔ A)) ∧
              Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
                (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 ∧
              let := BinaryGroupAction.action a.representation
              smallSupportGroup (HStar I)
                (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2 = X ∧
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                i.val = ⁅X,A⁆ ∧ f.factor i = ⁅X,A⁆ ⊔ A ∧ X ≤ f.product ∧
                ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
                  centralizer (f.product : Set (HStar I)) ∧
                f.product ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
                  (QuotientGroup.mk' (pCore 2 I)) = ⊤ ∧
                0 < Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ∧
                Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 ∧
                ∃ r : SelectedQuadraticEndpoint hf a,
                  (∀ D : Subgroup G, I ≤ normalizer (D : Set G) →
                    r.endpoint.conjugate (c.endpoint.conjugate D) = D) ∧
                  r.endpoint.representative * c.endpoint.representative ∈ I ∧
                  rank (actorImage I (r.endpoint.conjugate (F.UH I))) = 1 ∧
                  Nat.log 2 ((commutatorPreimage (F.UH I) (r.endpoint.conjugate (F.UH I))
                    (r.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 ∧
                  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
                  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
                  F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                  F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                  C ≤ F.UH I ∧ C ≤ c.endpoint.conjugate (F.UH I) ∧
                  IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                  s.image C = subspaceCommutator a.representation ⊤ A ∧
                  Module.finrank (ZMod 2) (s.image C) = 2 ∧
                  C = Chapter14.Section06.OddNormalizer.supportPreimage a (s.image C) ∧
                  F.Li L 1 ≤ normalizer (C : Set G) ∧
                  F.Li L 1 ≤ centralizer (F.Vi 1 : Set G) ∧
                  C ≤ Chapter14.Section06.OddNormalizer.supportPreimage a
                    (subspaceCommutator a.representation ⊤ i.val) ∧
                  c.endpoint.conjugate (F.Li L 1) ≤ normalizer (C : Set G) ∧
                  c.endpoint.conjugate (F.Li L 1) ≤
                    centralizer (c.endpoint.conjugate (F.Vi 1) : Set G) ∧
                  C ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1 ∧
                  C ⊓ centralizer (c.endpoint.conjugate (F.Li L 1) : Set G) =
                    c.endpoint.conjugate (F.Vi 1) ∧
                  ((Nat.card (conjugationImage (F.Li L 1) C) = 3 ∨
                    (Nat.card (conjugationImage (F.Li L 1) C) = 12 ∧
                      Nonempty (conjugationImage (F.Li L 1) C ≃* alternatingGroup (Fin 4)))) ∧
                    (Nat.card (conjugationImage (F.Li L 1) C) = 3 ↔
                      (F.Li L 1).pCoreIn 2 ≤ centralizer (C : Set G))) ∧
                  ((Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 3 ∨
                    (Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 12 ∧
                      Nonempty (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C ≃*
                        alternatingGroup (Fin 4)))) ∧
                    (Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 3 ↔
                      (c.endpoint.conjugate (F.Li L 1)).pCoreIn 2 ≤ centralizer (C : Set G))) ∧
                  (Nat.card (smallSupportFactors (HStar I)
                    (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                      c.endpoint.conjugate (F.UH I) ≤ S ∧
                      (∃ x : I, S = (x : G)⁻¹ • T) ∧
                      let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                      let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                      ((T : Subgroup G) ⊓ normalizer (K1 : Set G)).relIndex (T : Subgroup G) = 2 ∧
                      T1.relIndex (S : Subgroup G) = 2 ∧
                      T1 ≤ normalizer (C : Set G) ∧
                      I ⊓ normalizer (C : Set G) ≤ normalizer (K1 : Set G) ∧
                      ∃ P : Sylow 2 (I ⊓ normalizer (C : Set G) : Subgroup G),
                        (P : Subgroup (I ⊓ normalizer (C : Set G) : Subgroup G)).map
                          (I ⊓ normalizer (C : Set G)).subtype = T1) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,
      hr,hAc,hAd,hCX,hW,hcomp,hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,
      r,hlabels,hprod,hrr,hrd,hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,
      hLC,hLZ,hCS,hoppN,hoppZ,hfixed,hfixedOpp,hnormalizer⟩ :=
    local_minimal_five_common_normalizer h hab structural previous J hJ hne
  let := hU
  let := hXn
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let := hCE
  refine ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,hr,hAc,hAd,hCX,hW,hcomp,
    hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,r,hlabels,hprod,hrr,hrd,
    hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,hLC,hLZ,hCS,hoppN,hoppZ,
    hfixed,hfixedOpp,?_,?_,hnormalizer⟩
  · apply Theory.GroupAction.ElementaryEightPointResidual.residual_image _ _ _ _ hCc hf.point_card hLC hfixed
      (pointResidual_core_quotient_card h structural)
    rw [←residual_group h structural]
    exact isPPerfect_embedded_pResidual 2 _
  · let e : (F.Li L 1) ≃* c.endpoint.conjugate (F.Li L 1) :=
      (MulAut.conj c.endpoint.representative).subgroupMap (F.Li L 1)
    have hp : IsPPerfect 2 (F.Li L 1) := by
      rw [←residual_group h structural]
      exact isPPerfect_embedded_pResidual 2 _
    have hzOpp : Nat.card (c.endpoint.conjugate (F.Vi 1)) = 2 := by
      change Nat.card ((F.Vi 1).map (MulAut.conj c.endpoint.representative).toMonoidHom) = 2
      exact (Nat.card_congr ((MulAut.conj c.endpoint.representative).subgroupMap
        (F.Vi 1)).toEquiv).symm.trans hf.point_card
    have hquotOpp : Nat.card ((c.endpoint.conjugate (F.Li L 1)) ⧸
        pCore 2 (c.endpoint.conjugate (F.Li L 1))) = 3 :=
      (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans
        (pointResidual_core_quotient_card h structural)
    exact Theory.GroupAction.ElementaryEightPointResidual.residual_image _ _ _
      (hp.of_surjective e.toMonoidHom e.surjective)
      hCc hzOpp hoppN hfixedOpp hquotOpp

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
