module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The unique maximal overgroup in the original A₅ branch

The actual module proves T-normality of L. The local-component chain
theorem then makes every containing component T-normal, and A.4.10 makes
it faithful. Hypothesis13.3.1(4) gives that component its actual A₅ quotient;
proper Sylow overgroups in A₅ are solvable, so local rigidity identifies
it with L. Thus L is maximal in the full local family.

The genuine known-simple A/C theorems now give 1.2.7, with the T-orbit of
L equal to L. The unique maximal two-local is N_G(L), and the nontrivial
normal binary module places its full normalizer in N_G(L).

Source: Aschbacher–Smith 13.3.1(4),13.3.2,1.2.7–9 and13.1.2(5),
printed pp.884–885,506–507 and866.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter1.Section02 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The source minimal A₅ choice is maximal in the full local family. -/
theorem maximal_local : L ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hL := ((mem_faithfulLocalComponents_iff T L).mp d.hypothesis.local_component).1
  refine ⟨hL,?_⟩
  intro K hK hLK
  have hTK := local_chain_normalizes hL hK hLK d.normalizes_L
  have hN : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [inf_of_le_left d.normalizes_L,inf_of_le_left hTK]
  have hf := (faithful_chain_of_A410_of_normalizer_eq T (d.hypothesis.qtke.evenCharacteristic T)
    ChapterA.Section04.SourceChains.adequate_source d.hypothesis.local_component hK hLK hN).2
  obtain ⟨e⟩ := d.uniform_A5 K hf
  exact (Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hK hL hLK
    (SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP))).symm

/-- Genuine 1.2.7 identifies the actual unique maximal two-local as N_G(L). -/
theorem unique_maximal_overgroup :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
  have hu := nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.hypothesis.qtke T d.maximal_local
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    apply iSup_le
    intro t
    exact (mem_normalizer_iff_map_conj_eq.mp (d.normalizes_L t.property)).le
  simpa only [horbit] using hu.normalizer_unique

/-- The full module normalizer lies in the original local normalizer. -/
theorem module_normalizer : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le d.chosen.le_sylow) d.chosen.ne_bot
    (sup_le d.chosen.normalizes d.flag.T_normalizes)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
