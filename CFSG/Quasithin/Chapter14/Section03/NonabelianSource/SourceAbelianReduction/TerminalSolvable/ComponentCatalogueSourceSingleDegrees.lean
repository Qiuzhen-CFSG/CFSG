module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleActor

/-!
# Exact normalized A₅ degree alternatives for the original source

The original component selection, including the exchanged-source exclusions,
now leaves a normalized A₅ in degree four or eight, or L₂(8). In degree
eight the same actor has order eight and its centralizer of the selected
component has order two. The larger-actor branch supplies degree four;
the marked small-actor argument supplies all degree-eight data.

The final consumer applies these alternatives to literal terminal solvability.
It remains conditional on the ambient normalized A₅ exclusions owned by
this terminal-solvability task and the separately owned L₂(8) exclusion.
It does not assert original 14.3.15 without those source proofs.
Source: Aschbacher–Smith G.11.2 and 14.3.13–15, pp.364,993–994.
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

/-- The original catalogue selects normalized A₅ in degree four or eight,
with the exact actor and centralizer orders in degree eight, or L₂(8). -/
theorem source_normalized_a5_degree_cases
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∧
        (finrank (ZMod 2) (Additive F.Uhat) = 4 ∨
          (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
            finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
            Nat.card ((centralizer (F.terminalDot K : Set F.TerminalHdot)).subgroupOf
              (F.terminalDot (F.X g))) = 2))) ∨ EightImageRow F K) := by
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
      obtain ⟨K,hK,hknown | h8⟩ := s.local_lift_single_five_actor_or_eight
      · obtain ⟨hspan,he,he5,_,_,hd,hm,hc⟩ := hknown
        refine ⟨K,hK,Or.inl ⟨hspan,?_,Or.inr ⟨hd,hm,?_⟩⟩⟩
        · exact ⟨(MulEquiv.subgroupCongr he).trans he5.some⟩
        · simpa only [he] using hc
      · exact ⟨K,hK,Or.inr h8⟩
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
    exact ⟨K,hK,Or.inl ⟨hspan,he,Or.inl s.degree_eq_four⟩⟩

end Source

/-- The same literal source alternatives without auxiliary module instances. -/
theorem source_normalized_a5_card_cases
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
        (Nat.card F.Uhat = 16 ∨
          (Nat.card F.Uhat = 256 ∧ Nat.card (F.terminalDot (F.X g)) = 8 ∧
            Nat.card ((centralizer (F.terminalDot K : Set F.TerminalHdot)).subgroupOf
              (F.terminalDot (F.X g))) = 2))) ∨ EightImageRow F K) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  obtain ⟨K,hK,⟨hspan,he5,hd | ⟨hd,hm,hc⟩⟩ | h8⟩ :=
    source_normalized_a5_degree_cases hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hn
  · refine ⟨K,hK,Or.inl ⟨hspan,he5,Or.inl ?_⟩⟩
    change Nat.card (Additive F.Uhat) = 16
    norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
  · refine ⟨K,hK,Or.inl ⟨hspan,he5,Or.inr ⟨?_,?_,hc⟩⟩⟩
    · change Nat.card (Additive F.Uhat) = 256
      norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
    · change Nat.card (Additive (F.terminalDot (F.X g))) = 8
      norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hm]
  · exact ⟨K,hK,Or.inr h8⟩

/-- Apply the exact four/eight degree alternatives to the original
terminal-solvability input. The two normalized ambient exclusions stay
with this owner, and L₂(8) stays with its independent source owner. -/
theorem source_terminal_solvable_of_normalized_card_exclusions
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
    (hdouble : Nat.card F.Uhat = 256 → Nat.card (F.terminalDot (F.X g)) = 8 →
      ∀ K : Subgroup G, ComponentLift F g K →
      K = conjugateSpanBy K (T : Subgroup G) →
      (F.terminalDot K ≃* alternatingGroup (Fin 5)) →
      Nat.card ((centralizer (F.terminalDot K : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2 → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  obtain ⟨K,hK,⟨hspan,he5,hfour' | ⟨hd,hm,hc⟩⟩ | h8⟩ :=
    source_normalized_a5_card_cases hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hn
  · exact hfour hfour' K hK hspan he5.some
  · exact hdouble hd hm K hK hspan he5.some hc
  · exact height K hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
