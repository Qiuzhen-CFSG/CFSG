module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.BinaryG2Application
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.Reduction

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.BinaryG2Application`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion

open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem original_card_V (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) : Nat.card V = 64 := by
  have hd : Module.finrank (ZMod 2) (Additive V) = 6 :=
    s.coordinates.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [Nat.card_zmod, hd] at hc
  exact hc

private theorem original_faithful_core (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) :
    L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (L ⧸ pCore 2 L) := s.quotient.isSimpleGroup
  have hc := congrArg (map L.subtype) (s.chosen.centralizer_eq_core_of_simple
    s.quotient.isSimpleGroup)
  exact (show L ⊓ centralizer (V : Set G) = L.pCoreIn 2 by
    simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using hc).le

/-- The original odd actor's selected Theorem-B component admits the literal
binary-G₂ inner action, with no universal outer-solvability premise. -/
theorem unitary_original_selected_binary_derived_inner
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) (A : Subgroup G) [IsMulCommutative A]
    (hne : A ≠ ⊥) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        K ⊔ centralizer (K : Set (normalizer (A : Set G))) := by
  have h1223 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have h12 := h1223.toHypothesis1221
  have hcard : Nat.card V = 64 := original_card_V s
  have hfaith := original_faithful_core s
  obtain ⟨K,hK,_,_,_,hmodel,_,_⟩ :=
    chosen_oddNormalizer_exists_theoremB_component
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremB_knownSimple (G := X))
      h12 s.chosen hcard A hne hAN hcomm hodd hAV hunique hout
  have hi := chosen_oddNormalizer_inner_of_binary_derived_outer_section
    h12 s.chosen hfaith s.actor A hAN hcomm hodd hAV K hK hmodel
  exact ⟨K,hK,hmodel,hi⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
