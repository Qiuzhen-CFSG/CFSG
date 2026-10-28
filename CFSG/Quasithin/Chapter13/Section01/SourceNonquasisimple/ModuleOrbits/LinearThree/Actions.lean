module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Assembly
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SieveActions

/-!
# The L₃(2) quaternion branches in the source sieve

The genuine natural, doubled-natural and rank-four extension markings
already produce local quaternion actions on the original odd Frattini
plane. Including C_T(u)∩L in C_T(u) constructs the precise SieveActions
required by the centralizer consumer, alongside the earlier OrbitFacts.
The preceding classification owner supplies the markings on U.

Source: Aschbacher--Smith 13.1.12, printed pp.873--874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- A selected vector in the natural copy is T-central, so the noncentral
sieve has no representatives in this row. -/
theorem NaturalMarking.sieveActions (d : NaturalMarking L) (h : Context T L p) :
    SieveActions h where
  quaternion u s hnt _ := (hnt (d.selected_centralized h.sylow_normalizes
    ⟨u,s.mem⟩ s.local_sylow)).elim
  symmetric_three u s hnt _ := (hnt (d.selected_centralized h.sylow_normalizes
    ⟨u,s.mem⟩ s.local_sylow)).elim

/-- Both doubled-natural stabilizers give the literal quaternion sieve. -/
theorem DoubledNaturalMarking.sieveActions (d : DoubledNaturalMarking T L)
    (h : Context T L p) : SieveActions h := by
  apply sieveActions_of_component_quaternions h
  intro u s _
  exact d.selected_quaternion_action h ⟨u,s.mem⟩
    (fun he => s.ne_one (congrArg Subtype.val he)) s.local_sylow

/-- The rank-four nonfixed A₄ stabilizer gives the literal quaternion sieve. -/
theorem RankFourMarking.sieveActions (d : RankFourMarking L)
    (h : Context T L p) : SieveActions h := by
  apply sieveActions_of_component_quaternions h
  intro u s hnt
  exact d.selected_quaternion_action h ⟨u,s.mem⟩ s.local_sylow hnt

/-- All genuinely marked L₃(2) rows supply both inputs of the source
centralizer analysis, without an additional orbit or radical-action premise. -/
theorem centralizer_inputs_of_marked_linear_three
    (h : Context T L p)
    (hm : Nonempty (NaturalMarking L) ∨ Nonempty (DoubledNaturalMarking T L) ∨
      Nonempty (RankFourMarking L)) : OrbitFacts T L p ∧ SieveActions h := by
  refine ⟨orbitFacts_of_marked_linear_three h hm,?_⟩
  rcases hm with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact d.sieveActions h
  · exact d.sieveActions h
  · exact d.sieveActions h

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
