module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.SupportApplication
public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.PlaneFrattini

/-!
# The ambient plane action in the original singleton reduction

The same minimal outside subgroup and critical representative from the
odd-core counterexample now supply a Sylow subgroup of the full plane
centralizer. Frattini's argument lifts every action of its actual M-conjugate
to the normalizer of the original point centralizer. Both full Mc-spans lie
inside that point centralizer.

The two support orientations and original core denominators are retained.
These conclusions strengthen the exceptional E9:C4 branch; they do not
exclude it. Source: Aschbacher--Smith, 14.6.12, printed p.1031, using
14.1.18, Hypothesis 14.5.1 and F.9.13--17, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab


open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddCriticalPair.OrthogonalSource

/-- The original odd-core counterexample supplies the full ambient plane
action and both full abelian spans, with all earlier alternatives retained. -/
theorem source_oddCore_counterexample_nine_plane_frattini
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation,
        d.FittingFull ∧
        (Nat.card d.Index = 2 ∨
          (Nat.card d.Index = 1 ∧
            (ClassificationModels.IsTheoremEModel G ∨
              ((T : Subgroup G).relIndex J = 5 ∧
                ChapterF.Source.HypothesisF11
                  ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
                (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
                  Nat.card (conjugateSpanBy (localModule T M) J) = 64)) ∨
              (IsElementaryAbelian 3 (pResidual 2 (J ⧸ pCore 2 J)) ∧
                Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧
                Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤
                  (pResidual 2 (J ⧸ pCore 2 J))) = 4 ∧
                cubicRatio a.representation = 2 ∧
                Nat.card (J ⧸ pCore 2 J) = 36 ∧
                (∀ S : Sylow 2 (J ⧸ pCore 2 J), IsCyclic S ∧ Nat.card S = 4) ∧
                (∃ s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
                    (pResidual 2 (J ⧸ pCore 2 J)) 2,
                  (∃ t : T, (s.ambient 0).conjBy
                    (QuotientGroup.mk' (pCore 2 J) ⟨(t : G),hJ.1.1.2 t.property⟩) = s.ambient 1 ∧
                    (let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                     let R := fun k => ((pResidual 2 (A k)).map (A k).subtype).map J.subtype
                     (⁅conjugateSpanBy (localModule T M) J,R 0⁆ : Subgroup G).map
                       (MulAut.conj (t : G)).toMonoidHom =
                       ⁅conjugateSpanBy (localModule T M) J,R 1⁆)) ∧
                  (∀ k : Fin 2,
                    let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                    centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,
                      ((pResidual 2 A).map A.subtype).map J.subtype⁆) ∧
                  (let U := conjugateSpanBy (localModule T M) J
                   let Z := centralInvolutions T
                   let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                   let R := fun k => ((pResidual 2 (A k)).map (A k).subtype).map J.subtype
                   let W := fun k => ⁅U,R k⁆
                   (∀ k, W k = OddNormalizer.supportPreimage a
                     (subspaceCommutator a.representation ⊤ (s.ambient k))) ∧
                   (∀ k, Nat.card (W k) = 8) ∧ W 0 ⊓ W 1 = Z ∧
                   W 0 ⊔ W 1 = ⁅U,J⁆ ∧ Nat.card (⁅U,J⁆ : Subgroup G) = 32) ∧
                  (let D : ChapterF.Section09.Setup G :=
                     ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                   let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                     hG T hempty hM hu hmany hcard e hab J hJ.1
                   ∀ (i : h.CriticalEndpoint) (k : Fin 2),
                     let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                     let R := ((pResidual 2 A).map A.subtype).map J.subtype
                     let W := ⁅D.UH,R⁆
                     actorImage J (i.conjugate D.UH) ≤ normalizer (s.ambient k : Set (J ⧸ pCore 2 J)) ∧
                     i.conjugate D.UH ≤ normalizer (A.map J.subtype : Set G) ∧
                     i.conjugate D.UH ≤ normalizer (R : Set G) ∧
                     i.conjugate D.UH ≤ normalizer (W : Set G) ∧
                     i.conjugate D.V₁ ⊓ W = ⊥ ∧
                     ⁅(D.UH ⊓ i.conjugate D.QH) ⊓ W,i.conjugate D.UH⁆ = ⊥) ∧
                  (let D : ChapterF.Section09.Setup G :=
                     ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                   let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                     hG T hempty hM hu hmany hcard e hab J hJ.1
                   ∀ i : h.CriticalEndpoint,
                     let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                     let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
                     let E := D.UH ⊓ i.conjugate D.QH
                     let C := D.UH ⊓ centralizer (i.conjugate D.UH : Set G)
                     (∀ k, Nat.card (E ⊓ W k : Subgroup G) = 4) ∧
                     C = (E ⊓ W 0) ⊔ (E ⊓ W 1) ∧
                     Nat.card C = 8 ∧ C.relIndex E = 2) ∧
                  (let D : ChapterF.Section09.Setup G :=
                     ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                   let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                     hG T hempty hM hu hmany hcard e hab J hJ.1
                   ∀ i : h.CriticalEndpoint,
                     let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
                     let W := fun k => ⁅D.UH,((pResidual 2 (A k)).map (A k).subtype).map J.subtype⁆
                     let C := i.conjugate D.UH ⊓ centralizer (D.UH : Set G)
                     ∃ j : h.CriticalEndpoint,
                       (∀ B : Subgroup G, J ≤ normalizer (B : Set G) →
                         (i.conjugate B).map (MulAut.conj j.representative).toMonoidHom = B) ∧
                       C = (((D.UH ⊓ j.conjugate D.QH) ⊓ W 0) ⊔
                         ((D.UH ⊓ j.conjugate D.QH) ⊓ W 1)).conjBy j.representative⁻¹ ∧
                       Nat.card C = 8 ∧ C.relIndex (i.conjugate D.UH ⊓ D.QH) = 2)) ∧
                (let D : ChapterF.Section09.Setup G :=
                   ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                 let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                   hG T hempty hM hu hmany hcard e hab J hJ.1
                 3 ≤ h.b ∧ Odd h.b ∧
                   ∃ i : h.CriticalEndpoint,
                     i.representative ∉ Mc ∧ ¬ i.conjugate D.UH ≤ D.QH ∧
                     Nat.card (((i.conjugate D.UH).subgroupOf J).map
                       (QuotientGroup.mk' (pCore 2 J))) = 2 ∧
                     (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 ∧
                     commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
                       D.UH ⊓ i.conjugate D.QH ∧
                     commutatorPreimage (i.conjugate D.UH) D.UH D.V₁ =
                       i.conjugate D.UH ⊓ D.QH ∧
                     (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2 ∧
                     ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH⁆ = i.conjugate D.V₁ ∧
                     ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁ ∧
                     D.V₁ ⊔ i.conjugate D.V₁ ≤ ⁅D.UH,i.conjugate D.UH⁆ ∧
                     D.V₁ ⊓ i.conjugate D.V₁ = ⊥ ∧
                     Nat.card (D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) = 4 ∧
                     ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥ ∧
                     (D.UH = ⁅D.UH,J⁆ ∧ Nat.card D.UH = 32) ∧
                     (let A := D.V₁ ⊔ i.conjugate D.V₁
                      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
                      let K := centralizer (A : Set G)
                      (∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = C) ∧
                      K ⊔ normalizer (C : Set G) = normalizer (A : Set G) ∧
                      (∀ x ∈ normalizer (A : Set G),
                        ∃ c ∈ K, c * x ∈ normalizer (C : Set G)) ∧
                      conjugateSpanBy (localModule T M) Mc ⊔
                        i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ C) ∧
                     (let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
                      (C ⊓ J.pCoreIn 2).relIndex (J.pCoreIn 2) = 2 ∧
                      Nat.card ((C.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 4 ∧
                      C.relIndex J = 18 ∧
                      C = J ⊓ i.conjugate Mc ∧
                      Stellmacher.omegaOneCenterAmbient C = D.V₁ ⊔ i.conjugate D.V₁ ∧
                      (¬ normalizer (C : Set G) ≤ Mc) ∧
                      (¬ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) ≤ Mc) ∧
                      (∃ g : J,
                        Stellmacher.omegaOneCenterAmbient C = (localModule T M).conjBy (g : G) ∧
                        normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) = M.conjBy (g : G) ∧
                        normalizer (C : Set G) ≤ M.conjBy (g : G) ∧
                        J ⊓ normalizer (C : Set G) = (T : Subgroup G).conjBy (g : G)) ∧
                      ∃ S : Sylow 2 J,
                        C ≤ (S : Subgroup J).map J.subtype ∧
                        C.relIndex ((S : Subgroup J).map J.subtype) = 2 ∧
                        C ⊔ J.pCoreIn 2 = (S : Subgroup J).map J.subtype ∧
                        J ⊓ normalizer (C : Set G) = (S : Subgroup J).map J.subtype ∧
                        J ⊓ normalizer ((D.V₁ ⊔ i.conjugate D.V₁ : Subgroup G) : Set G) =
                          (S : Subgroup J).map J.subtype) ∧
                     ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
                       J ≤ normalizer (A : Set G) →
                       (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A))))) := by
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd,hcases⟩ :=
    source_oddCore_counterexample_nine_ambient_supports
      hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  refine ⟨J,hJ,hJH,hs,hU,a,f,d,hd,?_⟩
  rcases hcases with htwo | ⟨hone,hcases⟩
  · exact Or.inl htwo
  refine Or.inr ⟨hone,?_⟩
  rcases hcases with hmodel | hquintic |
    ⟨he,hnine,hdim,hq,horder,hSylow,hsupport,hb,ho,i,hi,hout,himage,hindex,
      hden,hden',hindex',hpoint,hpoint',hjoin,hinf,hfour,hcomm,hwhole,hcentral,j,hj⟩
  · exact Or.inl hmodel
  · exact Or.inr (Or.inl hquintic)
  exact Or.inr (Or.inr ⟨he,hnine,hdim,hq,horder,hSylow,hsupport,hb,ho,i,
    hi,hout,himage,hindex,hden,hden',hindex',hpoint,hpoint',hjoin,hinf,hfour,hcomm,
    hwhole,source_singleton_nine_plane_frattini
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i,hcentral,j,hj⟩)

end CFSG.Quasithin.Chapter14.Section06
