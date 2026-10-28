module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# Maximality of the original A₅ component

Faithfulness ascends along every local-component inclusion by passing to
the Sylow orbit groups. The uniform A₅ clause of Hypothesis 13.3.1 therefore
makes each upper component an A₅ section as well. Solvability of proper
Sylow overgroups in A₅ forces equality with the original component.

No chosen module or Sylow normalization of the component is required.
Source: Aschbacher–Smith, 13.3.2(2), pp.884–885, and 1.2.9, p.507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter1.Section02 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include h e

/-- The uniform A₅ branch is maximal before any normalization argument or
choice of irreducible module. -/
theorem maximal_local : L ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hL := ((mem_faithfulLocalComponents_iff T L).mp h.local_component).1
  refine ⟨hL, ?_⟩
  intro K hK hLK
  have hf := faithful_local_overgroup T (h.qtke.evenCharacteristic T)
    h.local_component hK hLK
  obtain ⟨eK⟩ := h.five_minimal ⟨e⟩ K hf
  exact (Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hK hL hLK
    (SolvableSylowOvergroups.of_equiv eK (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP))).symm

/-- The original A₅ component satisfies the full Chapter 12 entry hypothesis,
using the complete known-simple catalogue and no prior normalization. -/
theorem hypothesis1221 :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  have hfive : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let := hfive
  exact ⟨h.qtke, ⟨maximal_local h e,
    ((mem_faithfulLocalComponents_iff T L).mp h.local_component).2⟩,
    IsQuasisimple.of_mulEquiv e.symm⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
