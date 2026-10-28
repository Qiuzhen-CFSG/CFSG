module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceMarked

/-!
# Original terminal catalogue and its remaining source exclusions

The complete marked and exchanged recognition, larger-actor alternatives,
and A₆ exclusion give the component catalogue under the original E hypotheses.
For solvability we retain the marking proved in each branch. A marked
nonnormal component has the actual determinant tensor; a central-kernel
unmarked constituent is excluded through its A₇ orbit. The remaining
noncentral-kernel unmarked constituent is the paired direct-sum branch.
It still requires the original 12.8.13(7) exclusion and cannot be replaced
by a tensor ActionModel.

The final consumer has four explicit source obligations: normalized A₅
Borel noncontainment, the full tensor-span wreath quotient, the paired
source exclusion, and L₂(8). The first three and final assembly remain
with the terminal-solvability owner; L₂(8) retains its independent owner.
No unconditional terminal-solvability assertion is made.
Source: Aschbacher–Smith G.11.2(7),(12), 12.8.13(7), and 14.3.13–15,
printed pp.364,855–856,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

section Source
variable {G : Type*} [Group G] [Finite G]
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
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp

/-- The original component catalogue has no recognition callback: both
constituent branches and the larger-actor branch are now supplied. -/
theorem source_component_catalogue
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  source_component_catalogue_of_marked_images hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hyp hn (fun _ _ s => s.imageCases)

/-- The actual original quotient sieve leaves only A₅ and L₂(8), with all
component recognition and A₆ exclusion premises discharged. -/
theorem source_component_a5_or_eight
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      (Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∨ EightImageRow F K) :=
  source_component_a5_or_eight_of_marked_images hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hyp hn (fun _ _ s => s.imageCases)

/-- Refine the source catalogue while retaining the actual tensor witness.
The only unmarked branch left is the original noncentral constituent kernel,
which is the separate paired direct-sum case of G.11.2(12). -/
theorem source_normalized_or_tensor_or_paired
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    (∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5))) ∨
       EightImageRow F K ∨ Nonempty (ExchangedA5.ActionModel F K))) ∨
    ∃ (L : Subgroup F.TerminalHdot) (I : Submodule (ZMod 2) (Additive F.Uhat)),
      Nonempty (ExchangedPairedSource T M Mc F g B v L I) := by
  by_cases hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · have hfit := Recognition.original_terminal_fitting_centralizer_ne_bot
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
    obtain ⟨L,hL,hmove,hs,ho⟩ := hyp.exists_moved_component_orthogonal_selection hn hfit
    obtain ⟨hfix,hcom,I,hI,hirr,hspan,hdis,hform,hdim,hind⟩ := hs
    by_cases hv : v ∈ I
    · let s : MarkedSource T M Mc F g B v L I :=
        ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm,
          hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv⟩
      exact Or.inl s.normalized_a5_or_eight_or_tensor
    · by_cases hk : (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
          hI.invariant).toRepresentation.asGroupHom.ker ≤ center (componentOrbit L ⊤)
      · let s : ExchangedCentralSource T M Mc F g B v L I :=
          ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm,
            hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv,hk⟩
        exact s.false_of_source.elim
      · exact Or.inr ⟨L,I,⟨⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,
          hn,hyp,hm,hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv,hk⟩⟩⟩
  · let s : LargeActorSource T M Mc F g B v :=
      ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm⟩
    obtain ⟨K,hK,he,hspan⟩ := s.exists_normalized_a5_lift
    exact Or.inl ⟨K,hK,Or.inl ⟨hspan,he⟩⟩

/-- The original terminal action is solvable once the actual remaining
source exclusions are proved. No marked-image or tensor-construction input
remains. All four exclusions stay with their existing source owners. -/
theorem source_terminal_solvable_of_borel_wreath_paired_eight
    (hfieldFour : ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (hwreath : ∀ K : Subgroup G, ComponentLift F g K → ExchangedA5.ActionModel F K →
      Nonempty (((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath))
    (hpaired : ∀ (L : Subgroup F.TerminalHdot)
      (I : Submodule (ZMod 2) (Additive F.Uhat)),
      ExchangedPairedSource T M Mc F g B v L I → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  classical
  by_contra hn
  rcases source_normalized_or_tensor_or_paired hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hn with hknown | ⟨L,I,⟨s⟩⟩
  · obtain ⟨K,hK,hcases⟩ := hknown
    rcases hcases with h5 | hcases
    · obtain ⟨hspan,⟨e5⟩⟩ := h5
      obtain ⟨⟨eK⟩,_,_,_,_,_,hb⟩ := source_terminal_single_a5_parabolic
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e5 hspan
      have hnorm : (T : Subgroup G) ≤ normalizer (K : Set G) := by
        rw [hspan]
        exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
      exact hfieldFour K hK.local_component hnorm eK (hK.not_le hM.1.2 e) hb
    · rcases hcases with h8 | hm
      · exact height K hK h8
      · exact source_exchanged_a5_false_of_wreath hG T hempty hM hu hmany hcard e hnot
          F hne g hgP hgH hyp hK hm.some (hwreath K hK hm.some).some
  · exact hpaired L I s

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
