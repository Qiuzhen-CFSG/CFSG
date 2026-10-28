module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourMinus
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5NoSymmetric

/-!
# The genuine J₂/J₃ alternatives in original terminal solvability

The original catalogue and minus-core reduction now eliminate the entire
S₅ quotient branch. The same selected component is its full point
centralizer, with the actual I.4.7 local type. The terminal consumer retains
only ambient recognition of these types and the exact independent L₂(8)
exclusion. A second endpoint consumes actual equivalences to the concrete
J₂ and J₃ carriers and applies the original non-model hypothesis.

These recognition premises remain obligations of the terminal-solvability
owner; local types do not establish the ambient isomorphisms. The exact
eight-row exclusion retains its independent producer and final discharge.
Source: Aschbacher–Smith 14.2.17 and 14.3.15, printed pp.987 and 994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Terminal solvability now requires only the actual ambient exclusion of
the J₂/J₃ local types and the independently owned exact eight-row exclusion.
The full S₅ alternative is discharged from the original source hypotheses. -/
theorem source_terminal_solvable_of_janko_type_eight_exclusions
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
    (hjanko : Janko23.J2Type G ∨ Janko23.J3Type G → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  obtain ⟨K,hK,⟨hspan,⟨e5⟩,hd,_⟩ | h8⟩ := source_normalized_a5_minus_or_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn
  · obtain ⟨_,_,z,_,_,_,_,htype⟩ := source_single_a5_janko_type_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    exact hjanko htype
  · exact height K hK h8

/-- The remaining recognition inputs are actual isomorphisms to the two
concrete ATLAS carriers. The original non-model hypothesis then gives the
ambient contradiction; no family tag is treated as recognition. -/
theorem source_terminal_solvable_of_janko_recognition_eight_exclusion
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
    (hJ2 : Janko23.J2Type G → Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier))
    (hJ3 : Janko23.J3Type G → Nonempty (G ≃* Sporadic.Janko3.Model))
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_janko_type_eight_exclusions
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH ?_ height
  rintro (h2 | h3)
  · exact hnot (.janko_two (hJ2 h2))
  · exact hnot (.janko_three (hJ3 h3))

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
