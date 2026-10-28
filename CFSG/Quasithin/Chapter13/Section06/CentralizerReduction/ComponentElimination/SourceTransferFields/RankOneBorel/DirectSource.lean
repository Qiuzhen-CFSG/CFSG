module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.CharacteristicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.LocalNaturalGeometry

/-!
# Rank-one exclusion from the direct source geometry

The complete chi-zero orbit construction supplies the minimal natural
replacement from 13.6.16. The existing marked Borel calculation and the
universal earlier noncentrality statement then exclude the literal linear
and projective rank-one models. No distinguished-pair or C.1.26 callback
is retained. The direct natural-section geometry proves the E.2.3/Baumann image containment
on this literal action; no factor decomposition or Baumann callback is retained.

Source: Aschbacher–Smith 13.6.18, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
open ComponentSelection A5Module
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open Replacement.NaturalRecognition HigherFieldParabolics BorelGeometry.Placement
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (M : Subgroup G)
    (hv : orderOf (markedV d.module) = 2)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module))
      (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈
      Stellmacher.omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.module)))
    (hf : generalizedFitting (Gv (markedV d.module)) = pCore 2 (Gv (markedV d.module)))
    (h14 : ∀ D ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module),
      Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (D : Set G))
    (h15 : ∀ (D : Subgroup G)
      (hD : D ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module)),
      let := wk_elementary D L (T : Subgroup G) (markedZ d.module) (markedV d.module)
        hD.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed D L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
    (h16 : ∀ D ∈ Chapter1.LIn (Gv (markedV d.module))
      (Tv (T : Subgroup G) (markedV d.module)),
      Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (D : Set G) →
      ¬ D ≤ centralizer ({markedZ d.module} : Set G) →
      CharacteristicNormalizerObstruction (Tv (T : Subgroup G) (markedV d.module)) D)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G)))
    (h17 : ∀ D ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module),
      ∀ a : Tv (T : Subgroup G) (markedV d.module),
        (∃ g : G, (a : G) = MulAut.conj g (markedZ d.module)) →
        (checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict a ∈
          center (checkedSylowMap (T : Subgroup G) (markedV d.module)).range →
        ¬ D ≤ centralizer ({(a : G)} : Set G))
    (classification : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)


include hG hv hSylow hzOmega hf h14 h15 h16 h1324 h1325 hMV hBV hlocal h17
  classification

/-- Source 13.6.18 from the specified earlier source inputs and universal
13.6.17. The minimal replacement, its block and natural section, the marked
Borel and its checked fixation are all constructed in the proof. -/
theorem not_rank_one_of_direct_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      SL(2, F.Carrier)) := by
  rintro ⟨e⟩
  obtain ⟨_, K₀, _, hY, _, _, hn, _, _, _, _, hb, hpar, _, _, hs⟩ :=
    Replacement.exists_minimal_natural_block_of_characteristic_source hG K L (T : Subgroup G)
      (markedZ d.module) (markedV d.module) hv hL hz hSylow hzOmega hf hK
      h14 h15 h16 F e classification
  let := wk_elementary K₀ L (T : Subgroup G) (markedZ d.module) (markedV d.module)
    hY.1.1 hSylow hzOmega hf
  obtain ⟨s⟩ := hs
  have hmove : ¬ K₀ ≤ centralizer ({markedZ d.module} : Set G) := by
    intro hc
    exact (invariant_component_consequences K₀ L (T : Subgroup G)
      (markedZ d.module) (markedV d.module) hY hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff _ _ K₀ hY.1.1).mpr hc)
  obtain ⟨P, hP⟩ := hY.1.2.2.1
  have hPeq : (P : Subgroup (K₀ ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G)) =
      (Tv (T : Subgroup G) (markedV d.module)).subgroupOf
        (K₀ ⊔ Tv (T : Subgroup G) (markedV d.module)) := by
    apply map_injective (K₀ ⊔ Tv (T : Subgroup G) (markedV d.module)).subtype_injective
    rw [hP, map_subgroupOf_eq_of_le le_sup_right]
  have hfix := (BorelGeometry.source_component_centralizes_natural d K₀ M hL hz hY hn
    F.card_eq hb s (hG.involution_centralizer_sqtk hv) hzOmega
    (h16 K₀ hY.1 hn hmove) hSylow hf P hPeq (hpar P hP)
    h1324 h1325 hMV hBV hlocal).2
  apply h17 K₀ hY d.checkedPoint _ d.checkedPoint_central hfix
  obtain ⟨g, _, hg⟩ := exists_a_conjugator d.module
  exact ⟨g, hg.symm⟩

/-- The literal projective L₂(2ᵐ) exclusion in the notation of the book.
The canonical central quotient in characteristic two connects the actual
PSL₂ model to the linear model used by the module calculation. -/
theorem not_projective_rank_one_of_direct_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      PSL(2, F.Carrier)) := by
  rintro ⟨e⟩
  exact not_rank_one_of_direct_source hG d M hv hL hz hSylow hzOmega hf h14 h15 h16
    h1324 h1325 hMV hBV hlocal h17 classification K hK F
    ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
