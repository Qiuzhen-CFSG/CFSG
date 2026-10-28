module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceAssembly
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

/-!
# The remaining original source inputs to terminal solvability

Apply the assembled catalogue to the same terminal representation and form.
The normalized A₅ branch supplies its intrinsic two-core quotient and actual
Borel containment, so the original field-four Borel exclusion suffices.
In the exchanged branch the genuine tensor model supplies the numerical
bound, exact span quotient, and symplectic normalizer bound. The original
full wreath quotient then contradicts that bound.

Only marked-image recognition, normalized field-four Borel exclusion,
the actual exchanged tensor model and wreath quotient, and the L₂(8)
exclusion remain explicit. The marked-image producer owns the first and
tensor inputs; the eight-Borel producer owns the last. The two field-four
source arguments and unconditional final assembly remain with the
terminal-solvability owner. This conditional consumer is not a proof of
14.3.15 until these inputs are discharged.
Source: Aschbacher–Smith 14.3.6(1),(3) and 14.3.15, printed pp.991–994.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable {G : Type*} [Group G] [Finite G]

/-- The literal terminal-solvability consumer with all completed source
branches discharged. Every remaining input concerns the original carrier,
the same component, and its actual conjugate span. -/
theorem source_terminal_solvable_of_remaining_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hmarked : ∀ (L : Subgroup F.TerminalHdot)
      (I : Submodule (ZMod 2) (Additive F.Uhat))
      (s : MarkedSource T M Mc F g B v L I), s.ImageCases)
    (hfieldFour : ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (htensor : ∀ K : Subgroup G, ComponentLift F g K →
      F.terminalDot K ≃* alternatingGroup (Fin 5) →
      K ≠ conjugateSpanBy K (T : Subgroup G) →
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 →
      Nonempty (ExchangedA5.ActionModel F K))
    (hwreath : ∀ K : Subgroup G, ComponentLift F g K → ExchangedA5.ActionModel F K →
      Nonempty (((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath))
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  classical
  by_contra hn
  obtain ⟨K,hK,h5 | h8⟩ := source_component_a5_or_eight_of_marked_images
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn hmarked
  · obtain ⟨e5⟩ := h5
    by_cases hspan : K = conjugateSpanBy K (T : Subgroup G)
    · obtain ⟨⟨eK⟩,_,_,_,_,_,hb⟩ := source_terminal_single_a5_parabolic
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e5 hspan
      have hnorm : (T : Subgroup G) ≤ normalizer (K : Set G) := by
        rw [hspan]
        exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
      exact hfieldFour K hK.local_component hnorm eK (hK.not_le hM.1.2 e) hb
    · have hm := source_exchanged_a5_small_actor_of_non_normalized
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e5 hspan
      obtain ⟨m⟩ := htensor K hK e5 hspan hm
      exact source_exchanged_a5_false_of_wreath hG T hempty hM hu hmany hcard e hnot
        F hne g hgP hgH hyp hK m (hwreath K hK m).some
  · exact height K hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
