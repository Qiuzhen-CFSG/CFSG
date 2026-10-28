module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceDegrees
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceMultiplicityRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceIrreducible
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSix
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesFullFour

/-!
# The terminal A₆ exclusion and its original action adapters

The source theorem proves the A₆ exclusion from the original flag and
component hypotheses. The small-actor branch constructs a proper
constituent through the original point, obtains the Schur coordinates, and
recovers the natural Sylow diagram action. Degrees four and six force the
whole component action to be irreducible. The same-component kernel theorem
discharges the radical/two-core comparison in every numerical branch.

The final assembly constructs the literal G.10 action from the flag and applies
the proved larger-actor degree alternatives. No coordinate, action, radical or
numerical premise remains. The original conditional adapters retain their
public interfaces.
Source: Aschbacher--Smith 14.3.15, printed p.994, using G.11.2(2),(10).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original consumer; normalization and naturality are discharged
by the coordinates, leaving only their source recognition and larger radical. -/
theorem source_terminal_a6_false_of_coordinates_and_large_radical
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
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hc : Representation.BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp (F.terminalDot K).subtype))
    (hlarge : ¬ (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) →
      solvableRadical K = pCore 2 K) : False := by
  exact source_terminal_a6_false_of_action_and_large_radical
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e6
    (hK.alternatingSixNaturalAction_of_coordinates hG e6 hc) hlarge

/-- The actual 14.3.15 consumer in the irreducible component branch.
Its action input is proved; only the independently owned radical input remains. -/
theorem source_terminal_a6_false_of_irreducible_and_large_radical
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
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hi : Representation.IsIrreducible
      (F.terminalRepresentation.comp (F.terminalDot K).subtype))
    (hlarge : ¬ (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) →
      solvableRadical K = pCore 2 K) : False := by
  exact source_terminal_a6_false_of_action_and_large_radical
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e6
    (hK.alternatingSixNaturalAction_of_irreducible
      hG T hempty hM hu hmany hcard e F hne g hgP hgH e6 hi) hlarge

/-- The A₆ component exclusion in original 14.3.15. The original flag supplies
the elementary spaces and G.10 action; 14.3.14 supplies the numerical cases.
The natural diagram action and radical comparison concern this same K. -/
theorem source_terminal_a6_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_, he, hx, B, v, hyp, _⟩ :=
    Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  apply source_terminal_a6_false_of_terminal_degrees
    hG T hempty hM hu hmany hcard e F hnot hne g hgP hgH hK e6 hyp
  by_cases hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · exact Or.inl hm
  · let s : LargeActorSource T M Mc F g B v :=
      ⟨hG, hempty, hM, hu, hmany, hcard, ⟨e⟩, hnot, hne, hgP, hgH,
        hK.terminal_not_solvable, hyp, hm⟩
    rcases s.degree_cases with ⟨hd, _⟩ | ⟨hd, hm, _⟩
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ⟨hd, hm⟩)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
