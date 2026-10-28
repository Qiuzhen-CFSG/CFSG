module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourcePairedComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5Borel

/-!
# Terminal solvability after the exchanged tensor exclusion

The source component selection carries its genuine tensor coordinates
with the selected ambient lift. The tensor Borel contradiction removes
that branch and leaves normalized A₅ or L₂(8). The terminal-solvability
consumer constructs its action and geometry from the original rank-two
hypotheses and retains precisely those two Borel exclusions.

The final theorem applies this reduction to the original nonabelian
transfer consumer. Normalized field-four recognition remains with the
terminal-solvability owner; L₂(8) and the later transfer inputs retain
their separate source owners. This is conditional assembly, not yet
unconditional 14.3.15 or Theorem E.
Source: Aschbacher–Smith 14.3.5 and 14.3.13–16, pp.991–995.
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

/-- The actual tensor exclusion leaves only normalized A₅ and L₂(8).
The component, normal span and action coordinates are kept together. -/
theorem source_normalized_a5_or_eight
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5))) ∨ EightImageRow F K) := by
  obtain ⟨K,hK,hcases⟩ := source_normalized_or_tensor
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn
  rcases hcases with h5 | hrest
  · exact ⟨K,hK,Or.inl h5⟩
  · rcases hrest with h8 | hm
    · exact ⟨K,hK,Or.inr h8⟩
    · exact (source_exchanged_a5_false hG T hempty hM hu hmany hcard e hnot
        F hne g hgP hgH hyp hK hm.some).elim

/-- Terminal solvability now needs only the normalized field-four Borel
contradiction and the independently owned L₂(8) exclusion. -/
theorem source_terminal_solvable_of_borel_eight
    (hfieldFour : ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  obtain ⟨K,hK,⟨hspan,⟨e5⟩⟩ | h8⟩ := source_normalized_a5_or_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn
  · obtain ⟨⟨eK⟩,_,_,_,_,_,hb⟩ := source_terminal_single_a5_parabolic
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e5 hspan
    have hnorm : (T : Subgroup G) ≤ normalizer (K : Set G) := by
      rw [hspan]
      exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
    exact hfieldFour K hK.local_component hnorm eK (hK.not_le hM.1.2 e) hb
  · exact height K hK h8
end Source

variable {G : Type*} [Group G] [Finite G]

/-- The literal original terminal-solvability input, with all action,
geometry and catalogue premises constructed from the source prefix. Only
the two stated Borel exclusions remain for their source owners. -/
theorem source_terminal_solvable_of_two_borel_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hfieldFour : ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  exact source_terminal_solvable_of_borel_eight hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hyp hfieldFour height

/-- Apply the reduced terminal-solvability input to the original
nonabelian transfer consumer, retaining its independent later inputs. -/
theorem source_theoremE_of_nonabelian_of_two_borel_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hfieldFour : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
        (T : Subgroup G) ≤ normalizer (K : Set G) →
        (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
        ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (height : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
      ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False)
    (hself : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc))
    (hnonfusion : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        OutsidePointNonfusion F (sourceResidual M Mc))
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
    ?_ hself hnonfusion hcollapse hne
  intro hnot F hneF g hgP hgH
  obtain ⟨hcard,⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  exact source_terminal_solvable_of_two_borel_exclusions hG T hempty hM hu hmany
    hcard e hnot F hneF g hgP hgH (hfieldFour hnot) (height hnot F hneF g hgP hgH)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
