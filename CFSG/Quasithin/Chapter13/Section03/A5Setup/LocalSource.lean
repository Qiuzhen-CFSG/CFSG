module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The original A₅ local entry before choosing a coordinate flag

The genuine Irr⁺ choice already normalizes its component by T. Along a
containing local-component chain, A.4.10 preserves faithful membership;
Hypothesis 13.3.1(4) therefore makes the upper quotient A₅. Its solvable
proper Sylow overgroups force equality. The actual component is consequently
maximal and 1.2.7 gives its unique maximal two-local normalizer.

This constructs the normalizer input to the A₅ module marking directly from
the original chosen module. No normalizer action, flag or A₅ Context is an
input. Only T-invariance of the chosen V is retained from 13.3.2(3).
Source: Aschbacher–Smith 13.3.2(2), pp.884–885, and 1.2.7–9, pp.506–507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup
open Chapter1.Section02 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}
  (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
  (d : Chapter12.Section02.ChosenModule T L V)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include h d e

/-- The A₅ minimal choice is maximal before any flag or normalizer action
has been supplied. The component normalization is part of the Irr⁺ choice. -/
theorem maximal_local : L ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hL := ((mem_faithfulLocalComponents_iff T L).mp h.local_component).1
  refine ⟨hL, ?_⟩
  intro K hK hLK
  have hTK := local_chain_normalizes hL hK hLK d.sylow_normalizes_component
  have hN : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [inf_of_le_left d.sylow_normalizes_component, inf_of_le_left hTK]
  have hf := (faithful_chain_of_A410_of_normalizer_eq T (h.qtke.evenCharacteristic T)
    ChapterA.Section04.SourceChains.adequate_source h.local_component hK hLK hN).2
  obtain ⟨eK⟩ := h.five_minimal ⟨e⟩ K hf
  exact (Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hK hL hLK
    (SolvableSylowOvergroups.of_equiv eK (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP))).symm

/-- Original 1.2.7 applies to the same component and its actual T-orbit. -/
theorem normalizer_maximal_unique :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
  have hu := nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.qtke T (maximal_local h d e)
  simpa only [d.localOrbit_eq] using
    And.intro hu.normalizer_maximal hu.normalizer_unique

/-- The original source module normalizer is controlled without first
assuming that its action extends to five-point permutations. -/
theorem module_normalizer
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  normalizer_le_of_unique_maximalTwoLocal (normalizer_maximal_unique h d e).2
    (T.isPGroup'.to_le d.le_sylow) d.ne_bot (sup_le d.normalizes hTV)

end CFSG.Quasithin.Chapter13.Section03.A5Setup
