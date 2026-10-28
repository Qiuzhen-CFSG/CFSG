module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Components
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.ComponentNormality

/-!
# The two remaining normalizer cases for the original Hall kernel

Component detection and the five-row exclusion give a normal ordinary
component of the literal N_G(A) when its two-core is trivial. Applied to
the escaping elementary subgroup of the actual H-star Hall kernel, this
leaves a precise dichotomy: the genuine contrary C.2.8 configuration, or
a normal ordinary component outside M moved by the original full module.
The component carries the full Theorem B central-quotient catalogue.

This is an intermediate reduction, not 4.4.3 or Hall faithfulness. The
same owner qt-d-10-nona5-hall-faithfulness must prove module fixation,
exclude the C.2.8 case, and finish the normal-component placement and
inspection. All subgroups and actions retain the original G, T and L.
Source: Aschbacher--Smith, 4.4.6--11, printed pp.620--621, and 10.2.3(2),
printed p.745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The trivial-two-core case supplies a normal component with its full
source catalogue, without an A₅ marking or a model callback. -/
theorem source_nonnormal_oddNormalizer_normal_component_of_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L)) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hc : pCore 2 (normalizer (B : Set G)) = ⊥) :
    ∃ K : Subgroup (normalizer (B : Set G)),
      IsComponent (normalizer (B : Set G)) K ∧ K.Normal ∧
      ⁅K,D.fullModule.subgroupOf (normalizer (B : Set G))⁆ = K ∧
      ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) := by
  obtain ⟨K,hK,hm,hout,hcore,_,_,hFK,_⟩ :=
    source_nonnormal_oddNormalizer_moved_component_of_twoCore D hn B hne hBC hodd hBV hc
  exact ⟨K,hK,source_oddNormalizer_component_normal_of_twoCore D B hne hBC hodd hBV hc
    K hK hout hFK,hm,hout,hcore,source_oddNormalizer_component_theoremB D B hne K hK⟩

/-- The literal escaping Hall-kernel actor has either the contrary C.2.8
configuration or a normal moved component. Module fixation remains explicit. -/
theorem source_hstar_hall_kernel_normalizer_reduction
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥)
    (hfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      ((∃ (J X : Subgroup G)
          (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
          X ⊓ D.maximalLocal < X ∧
          ChapterC.HypothesisC28 KnownSimple.IsKnownSimple X (X ⊓ D.maximalLocal)
            ((solvableResidual (L ⊓ X : Subgroup G)).map (L ⊓ X).subtype) (J.pCoreIn 2)
            (Chapter4.Section02.Unitary.fullModule (localOrbit T L)
              ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
                (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
          ¬ X ⊓ D.maximalLocal ≤ normalizer
            ((solvableResidual (L ⊓ X : Subgroup G)).map (L ⊓ X).subtype : Set G)) ∨
        (pCore 2 (normalizer (A : Set G)) = ⊥ ∧
          ∃ K : Subgroup (normalizer (A : Set G)),
            IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
            ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
            ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
            pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K))) := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hAV : A ≤ centralizer (D.fullModule : Set G) := (le_inf hAY hAC).trans hfix
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk]
    exact ho.pow
  refine ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,?_⟩
  by_cases hc : pCore 2 (normalizer (A : Set G)) = ⊥
  · exact Or.inr ⟨hc,source_nonnormal_oddNormalizer_normal_component_of_twoCore
      D hn A hA hAC hodd hAV hc⟩
  · exact Or.inl (source_oddPrimeNormalizer_twoCore_counterexample D hn ho A
      (IsElementaryAbelian.isPGroup p A) hAC hAV hAT hout hc)

end CFSG.Quasithin.Chapter10
