module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Noncentrality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.DirectSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.CharacteristicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.SourceReplacement

/-!
# Source field exclusions from the complete local action theorems

The genuine characteristic block-orbit source and the natural-section
Baumann calculation discharge C.1.26 and E.2.3 on the actual local actors.
The complete adequate B.5 classification and A/C component generation are
also supplied here. The rank-one exclusion constructs its own replacement,
natural action, Borel geometry, checked fixation and noncentrality contradiction.
The common consumer retains the same literal quotient for 13.6.17--19.
Only the original earlier Chapter 13 source hypotheses remain explicit.

Source: Aschbacher--Smith 13.6.17--19, printed pp.930--931.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ComponentSelection A5Module SourceContainment.RankTwo.LocalApplication
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open RankOneBorel.Replacement.NaturalRecognition HigherFieldParabolics
open RankOneBorel.BorelGeometry.Placement
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete A/C source supplies A.3.9 on every literal reduced quotient. -/
private theorem source_component_generation (X : Type u) [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥) :
    cComponentLayer X = solvableResidual X :=
  ChapterA.Section03.SourceComponents.generation
    (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO

section RankOne
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
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
    (standing : SourceHypothesis T L)
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hidx : (Tv (T : Subgroup G) (markedV d.module)).relIndex (T : Subgroup G) = 2)
    (hzGlobal : markedZ d.module ∈ omegaOneCenterAmbient (T : Subgroup G))

include standing h63 hidx hzGlobal hv hSylow hzOmega hf h14 h15 h16 h1324 h1325 hMV hBV hlocal

/-- Source 13.6.18 for the literal projective rank-one model. Universal
13.6.17 is proved here for every replacement in Y_z, and is not a premise. -/
theorem lemma_13_6_18_of_direct_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      PSL(2, F.Carrier)) := by
  apply RankOneBorel.not_projective_rank_one_of_direct_source standing.qtke d M hv hL hz
    hSylow hzOmega hf h14 h15 h16 h1324 h1325 hMV hBV hlocal
    (classification := adequateClassification_knownSimple) (h17 := ?_) K hK F
  intro D hD a hag ha
  exact noncentral_of_checkedSylow_conjugate T L D (markedZ d.module) (markedV d.module)
    standing source_component_generation h63 hD (h14 D hD) hSylow hidx (d.V_le_T (map_mem d.module _))
    (by rw [← hv]; exact pow_orderOf_eq_one _) hzGlobal (markedZ_ne_one d.module)
    hf a hag ha

/-- The equivalent actual linear rank-one exclusion in characteristic two. -/
theorem not_linear_rank_one_of_direct_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      SL(2, F.Carrier)) := by
  rintro ⟨e⟩
  exact lemma_13_6_18_of_direct_source d M hv hL hz hSylow hzOmega hf h14 h15 h16
    h1324 h1325 hMV hBV hlocal standing h63 hidx hzGlobal K hK F
    ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩

/-- A common source consumer of 13.6.17–19. The same selected component,
marked seed, quotient map and field occur in all three conclusions. -/
theorem source_noncentrality_and_field_exclusions_of_direct_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hW : WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module) ∈
      Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) (markedV d.module)))
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (F : BinaryField) :
    (∀ a : Tv (T : Subgroup G) (markedV d.module),
      (∃ g : G, (a : G) = MulAut.conj g (markedZ d.module)) →
      (checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict a ∈
        center (checkedSylowMap (T : Subgroup G) (markedV d.module)).range →
      ¬ K ≤ centralizer ({(a : G)} : Set G)) ∧
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      PSL(2, F.Carrier)) ∧
    (1 < F.degree →
      ¬ (Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        SL(3, F.Carrier)) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        Atlas.G2.Model F.Carrier))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact noncentral_of_checkedSylow_conjugate T L K (markedZ d.module) (markedV d.module)
      standing source_component_generation h63 hK (h14 K hK) hSylow hidx (d.V_le_T (map_mem d.module _))
      (by rw [← hv]; exact pow_orderOf_eq_one _) hzGlobal (markedZ_ne_one d.module) hf
  · exact lemma_13_6_18_of_direct_source d M hv hL hz hSylow hzOmega hf h14 h15 h16
      h1324 h1325 hMV hBV hlocal standing h63 hidx hzGlobal K hK F
  · intro hm
    exact lemma_13_6_19_of_characteristic_source K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz
      adequateClassification_knownSimple standing.qtke hA36 F.card_eq hm hv hK (h14 K hK)
      hSylow hzOmega hf hW h16

end RankOne
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
