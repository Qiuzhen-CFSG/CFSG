module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import Theory.Representation.HexacodeAction.ReducedCover

/-!
# The intrinsic quotient in the covered-six branch

The concrete triple-cover image has three-rank at least two. Cyclic Sylow
three-subgroups rule out smaller source rank, while SQTK bounds it by two.
The proved A.3.6 rank argument therefore gives intrinsic quasisimplicity.
Schur's multiplier bound now makes the original map K/O₂(K) → K⁺ injective:
its target is already the full odd triple cover of A₆.

The isomorphism below is the actual induced plus map on every representative.
The original-flag consumer discharges the A.3.6 and plus two-core inputs.
This supplies the intrinsic quotient required by the covered-six action
and normalizer argument; it does not assert shortness of K.

Source: Aschbacher–Smith 13.6.22, printed p.932, and A.3.6, pp.43–45.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixIntrinsic
open ComponentSelection SourceContainment.RankTwo.LocalApplication
open SourceTransferFields.RankOneBorel
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}

private theorem source_three_rank
    (hG : IsSimpleQTKE 𝒦 G) (K L T : Subgroup G) (z v : G)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* Atlas.Codes.HexEvenAutomorphisms) :
    primeRank 3 K = 2 := by
  have hr : primeRank 3 K ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hK.1.1) (inclusion_injective hK.1.1)).trans
      ((hG.involution_centralizer_sqtk hv).stronglyQuasithin 3 (by decide) (by decide))
  by_contra hne
  let P : Sylow 3 K := Classical.choice inferInstance
  let f := e.toMonoidHom.comp (toPlusImage K L T z v hK.1.1 hL hz)
  have hsmall := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f
    (e.surjective.comp (toPlusImage_surjective K L T z v hK.1.1 hL hz))
  have hlarge := Representation.Hexacode.two_le_primeRank_even
  omega

/-- The induced original plus map has trivial kernel in the covered-six row. -/
theorem intrinsicTwoCoreToPlus_injective
    (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Function.Injective (intrinsicTwoCoreToPlus K L T z v hL hz hK hR) := by
  let := (source_intrinsic_quasisimple hG hA36 K L T z v hv hK
    (source_three_rank hG K L T z v hv hK hL hz e)).1
  have hi := Representation.Hexacode.injective_of_surjective_of_twoCore_eq_bot
    (pCore_quotient_pCore_eq_bot 2)
    (e.toMonoidHom.comp (intrinsicTwoCoreToPlus K L T z v hL hz hK hR))
    (e.surjective.comp (intrinsicTwoCoreToPlus_surjective K L T z v hL hz hK hR))
  intro x y hxy
  exact hi (congrArg e hxy)

/-- The original covered-six component modulo its two-core, with the
literal plus-map marking retained. -/
noncomputable def intrinsicPlusEquiv
    (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* Atlas.Codes.HexEvenAutomorphisms) :
    (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K :=
  MulEquiv.ofBijective (intrinsicTwoCoreToPlus K L T z v hL hz hK hR)
    ⟨intrinsicTwoCoreToPlus_injective hG hA36 K L T z v hv hK hL hz hR e,
      intrinsicTwoCoreToPlus_surjective K L T z v hL hz hK hR⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original flag supplies an isomorphism on the exact component map,
without a minimal replacement or any extra kernel assumption. -/
theorem marked_intrinsic_equiv_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceContainment.RankTwo.LocalApplication.SourceHypothesis T L)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* Atlas.Codes.HexEvenAutomorphisms) :
    ∃ E : (K ⧸ pCore 2 K) ≃* plusImage K L (T : Subgroup G)
        (markedZ d.flag.module) (markedV d.flag.module) hL hz K,
      ∀ k : K, E (QuotientGroup.mk' (pCore 2 K) k) =
        componentMap K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hL hz k := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hR := SourceContainment.LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
    K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
    hK.1.1 hL hz hSylow
  refine ⟨intrinsicPlusEquiv standing.qtke
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    K L (T : Subgroup G) _ _ (marked_orders d.flag.module).2 hK hL hz hR e, ?_⟩
  intro k
  apply Subtype.ext
  exact toPlusImage_apply K L (T : Subgroup G) _ _ hK.1.1 hL hz k

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixIntrinsic
