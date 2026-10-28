module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# The B.5 moved-space assertion in the original 13.6.15 action

All classifier premises come from the original local plus action and the
complete known-simple adequate classifier. Thus the originally marked A₅
constituent is exactly [W_K,K⁺], and W_K is its direct sum with C_W_K(K⁺).
This is the first sentence of the proof of 13.6.15, retaining the same
constituent and its same coordinates for the later transposition argument.
Source: Aschbacher–Smith, 1 March 2004 manuscript, printed p.930, PDF p.947.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
open ChapterB.QuasisimpleSource ChapterB.SourceInduction ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal 13.6.15 constituent supplies the whole moved module and its
fixed complement, with no remaining classifier or action decomposition input. -/
theorem wk_moved_and_isCompl
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    ∀ I : Subrepresentation (componentRepresentation K L T z v hL hz),
      ActionEquiv I.toRepresentation (alternatingNatural 5) →
      I.toSubmodule = moved (wkRepresentation K L T z v hL hz)
        (plusImage K L T z v hL hz K) ∧
      IsCompl I.toSubmodule (fixedSpace (wkRepresentation K L T z v hL hz)
        (plusImage K L T z v hL hz K)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  dsimp only
  intro I e
  have ha := classifierApplicability_of_local hG K L T z v hv hL hz hSylow hzOmega hf hK hn
  have hc := plusImage_K_quasisimple K L T z v hL hz hK ha.twoCore
  exact moved_and_isCompl_of_classifier ha hc I e adequateClassification_knownSimple


/-- The ambient plus actor acts by permutations in the original constituent's
coordinates, extending the original K⁺ marking. -/
theorem wk_permutation_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    ∀ (I : Subrepresentation (componentRepresentation K L T z v hL hz))
      (e : ActionEquiv I.toRepresentation (alternatingNatural 5)),
      ∃ r : Gplus K L T z v hL hz →* Equiv.Perm (Fin 5),
        (∀ c : plusImage K L T z v hL hz K,
          r c = (e.groupEquiv c : Equiv.Perm (Fin 5))) ∧
        ∀ g (w : I.toSubmodule), wkRepresentation K L T z v hL hz g
          (w : Additive (WK K L T z v)) =
          (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5)
            (r g) (e.linearEquiv w)) : Additive (WK K L T z v)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  dsimp only
  intro I e
  let := plusImage_K_normal K L T z v hL hz hK hn
  have hm := (wk_moved_and_isCompl hG K L T z v hv hL hz hSylow hzOmega hf hK hn I e).1
  exact exists_permutation_action_of_eq_moved
    (ρ := wkRepresentation K L T z v hL hz)
    (C := plusImage K L T z v hL hz K) I e hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
