module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleDouble

/-!
# Only the degree-four normalized A₅ and L₂(8) remain

The actual marked small-actor A₅ is excluded by its normal cubic centralizer.
The exchanged rows are already excluded on their literal source actions.
The larger-actor branch therefore supplies the only surviving A₅, in degree
four, with the same selected lift and T-conjugate span.

The final theorem applies this reduction to original terminal solvability.
The ambient degree-four A₅ recognition and independent L₂(8) exclusion remain
explicit; this is not yet unconditional 14.3.15.
Source: Aschbacher–Smith G.11.8 and 14.3.13–15, pp.368–369,993–994.
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

/-- The original nonsolvable source selects normalized A₅ in degree four, or L₂(8). -/
theorem source_normalized_a5_four_or_eight
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∧
        finrank (ZMod 2) (Additive F.Uhat) = 4) ∨ EightImageRow F K) := by
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
      obtain ⟨K,hK,h8⟩ := s.local_lift_eight
      exact ⟨K,hK,Or.inr h8⟩
    · by_cases hk : (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
          hI.invariant).toRepresentation.asGroupHom.ker ≤ center (componentOrbit L ⊤)
      · let s : ExchangedCentralSource T M Mc F g B v L I :=
          ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm,
            hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv,hk⟩
        exact s.false_of_source.elim
      · let s : ExchangedPairedSource T M Mc F g B v L I :=
          ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm,
            hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv,hk⟩
        exact s.false_of_source.elim
  · let s : LargeActorSource T M Mc F g B v :=
      ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm⟩
    obtain ⟨K,hK,he,hspan⟩ := s.exists_normalized_a5_lift
    exact ⟨K,hK,Or.inl ⟨hspan,he,s.degree_eq_four⟩⟩

end Source
/-- The same alternatives without auxiliary module instances. -/
theorem source_normalized_a5_four_card_or_eight
    {G : Type*} [Group G] [Finite G]
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
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∧
        Nat.card F.Uhat = 16) ∨ EightImageRow F K) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  obtain ⟨K,hK,⟨hspan,he5,hd⟩ | h8⟩ :=
    source_normalized_a5_four_or_eight hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hn
  · refine ⟨K,hK,Or.inl ⟨hspan,he5,?_⟩⟩
    change Nat.card (Additive F.Uhat) = 16
    norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
  · exact ⟨K,hK,Or.inr h8⟩

/-- Terminal solvability needs only the degree-four ambient exclusion and the exact L₂(8) source exclusion. -/
theorem source_terminal_solvable_of_four_eight_exclusions
    {G : Type*} [Group G] [Finite G]
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
    (hfour : Nat.card F.Uhat = 16 → ∀ K : Subgroup G, ComponentLift F g K →
      K = conjugateSpanBy K (T : Subgroup G) →
      (F.terminalDot K ≃* alternatingGroup (Fin 5)) → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  obtain ⟨K,hK,⟨hspan,he5,hfour'⟩ | h8⟩ :=
    source_normalized_a5_four_card_or_eight hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hn
  · exact hfour hfour' K hK hspan he5.some
  · exact height K hK h8

/-- Apply the reduced terminal-solvability input to the original
nonabelian transfer consumer, retaining its independent later inputs. -/
theorem source_theoremE_of_nonabelian_of_four_eight_exclusions
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hfour : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Nat.card F.Uhat = 16 →
      ∀ K : Subgroup G, ComponentLift F g K → K = conjugateSpanBy K (T : Subgroup G) →
        (F.terminalDot K ≃* alternatingGroup (Fin 5)) → False)
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
  exact source_terminal_solvable_of_four_eight_exclusions hG T hempty hM hu hmany
    hcard e hnot F hneF g hgP hgH (hfour hnot F hneF g hgP hgH) (height hnot F hneF g hgP hgH)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
