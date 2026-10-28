module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FaithfulComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# Clause two on the original central quotient

Because the B.5 moved space is the whole chosen space, nonsplitting means
precisely that the original component has a nonzero fixed space. The
canonical quotient intertwiner transports every clause-two natural row to
the original L/C_L(V) action, retaining the quotient representative formula
from CentralComparison.
Source: Aschbacher--Smith B.5.1(2) and 12.2.2, pp.99,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
open ChapterB.QuasisimpleSource
variable {A B X Y : Type*} [Group A] [Group B]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
  {ρ : Representation (ZMod 2) A X} {σ : Representation (ZMod 2) B Y}

theorem nonsplitNatural_of_equiv (e : ActionEquiv ρ σ)
    (h : NonsplitNatural σ) : NonsplitNatural ρ := by
  cases h with
  | linearTwo F he => obtain ⟨a⟩ := he; exact .linearTwo F ⟨e.trans a⟩
  | symplectic F he => obtain ⟨a⟩ := he; exact .symplectic F ⟨e.trans a⟩
  | g2 F he => obtain ⟨a⟩ := he; exact .g2 F ⟨e.trans a⟩
  | alternatingSix he => obtain ⟨a⟩ := he; exact .alternatingSix ⟨e.trans a⟩
  | alternatingEight he => obtain ⟨a⟩ := he; exact .alternatingEight ⟨e.trans a⟩
  | derivedG2 he => obtain ⟨a⟩ := he; exact .derivedG2 ⟨e.trans a⟩
  | linearThree he => obtain ⟨a⟩ := he; exact .linearThree ⟨e.trans a⟩

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

theorem fixedSpace_eq_invariants : fixedSpace ρ K = D.chosenAction.invariants := by
  ext v
  constructor
  · intro hv l
    have hh := hv (c.projection (QuotientGroup.mk' (pCore 2 L) l))
    change ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v = v at hh
    rwa [c.action,D.quotientAction_mk] at hh
  · intro hv k
    obtain ⟨q,rfl⟩ := c.surjective k
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    change ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v = v
    rw [c.action,D.quotientAction_mk]
    exact hv l

/-- Literal nonsplitting is equivalent to a nonzero original fixed space. -/
theorem nonsplitting_iff_fixed_ne_bot (s : MovedSection ρ K) :
    (¬ IsCompl s.space.toSubmodule (fixedSpace ρ K)) ↔
      D.chosenAction.invariants ≠ ⊥ := by
  rw [c.space_eq_top s,c.fixedSpace_eq_invariants]
  constructor
  · intro hn hz
    exact hn (hz ▸ isCompl_top_bot)
  · intro hn hc
    exact hn (eq_bot_of_top_isCompl hc)

/-- All seven clause-two constructors on the literal faithful central action. -/
theorem corrected_clause_two
    (b : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hn : D.chosenAction.invariants ≠ ⊥) :
    letI := D.actionCentralizer_normal
    NonsplitNatural D.faithfulCentralAction := by
  let := D.actionCentralizer_normal
  exact ModuleClassification.nonsplitNatural_of_equiv (c.faithfulCentralMarking b.sectionData)
    (b.clause_two ((c.nonsplitting_iff_fixed_ne_bot b.sectionData).mpr hn)).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
