module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.SupportAction

/-!
# Original elementary-nine consumer with actual lifted supports

The same J, quotient action and ratio decomposition from the original
odd-core counterexample carry the two lifted cubic supports. Each has
order eight; their intersection is Z and their join is [U,J] of order32.
The same original Sylow element exchanges the literal commutator supports.
Every original critical span normalizes these supports and their full
residual lifts. The opposite point meets neither support, so each support's
intersection with the literal critical core denominator centralizes the
opposite span. The reciprocal core and point-line geometry is retained.

This is a geometric reduction of the ambient-nine branch, not its
exclusion. No exchanged-dihedral-factor or 14.6.13 alternative is used.
Source: Aschbacher--Smith, 14.6.2 and 14.6.12, pp.1021,1031, and
F.9.13--17, pp.322--324 of refs/quasithin.pdf.
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

/-- The original counterexample reduction retains all critical core data
and constructs the literal lifted-support action in its nine branch. -/
theorem source_oddCore_counterexample_nine_support_action
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
                     ⁅(D.UH ⊓ i.conjugate D.QH) ⊓ W,i.conjugate D.UH⁆ = ⊥)) ∧
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
                     ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
                       J ≤ normalizer (A : Set G) →
                       (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A))))) := by
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd,hcases⟩ :=
    source_oddCore_counterexample_nine_ambient_geometry
      hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  refine ⟨J,hJ,hJH,hs,hU,a,f,d,hd,?_⟩
  rcases hcases with htwo | ⟨hone,hcases⟩
  · exact Or.inl htwo
  refine Or.inr ⟨hone,?_⟩
  rcases hcases with hmodel | hquintic | ⟨he,hnine,hdim,hq,horder,hSylow,⟨s,hex,hZ⟩,hcrit⟩
  · exact Or.inl hmodel
  · exact Or.inr (Or.inl hquintic)
  have hgeo := source_singleton_nine_lifted_supports
    hG T hempty hM hu hmany hcard e hab J hJ hs a s
  obtain ⟨t,ht⟩ := hex
  refine Or.inr (Or.inr ⟨he,hnine,hdim,hq,horder,hSylow,⟨s,⟨t,ht,?_⟩,hZ,hgeo,?_⟩,hcrit⟩)
  · dsimp only
    have hw0 := hgeo.1 0
    have hw1 := hgeo.1 1
    dsimp only at hw0 hw1
    rw [hw0,hw1]
    let tJ : J := ⟨(t : G),hJ.1.1.2 t.property⟩
    have hh := OddNormalizer.supportPreimage_conjugate a
      (subspaceCommutator a.representation ⊤ (s.ambient 0)) tJ
    have ht' : (s.ambient 0).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 J) tJ)).toMonoidHom = s.ambient 1 := ht
    rw [moved_map_conjugate,ht'] at hh
    exact hh
  · dsimp only
    intro i k
    have hn := source_singleton_nine_critical_support_normalizers
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
      (s.ambient k) (map_subtype_le _) i
    exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,
      source_singleton_nine_critical_point_support_disjoint
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine s i k,
      source_singleton_nine_denominator_support_centralizes
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine s i k⟩

end CFSG.Quasithin.Chapter14.Section06
