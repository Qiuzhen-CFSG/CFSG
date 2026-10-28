module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Doubled

/-!
# The literal local quaternion actions in the L₃(2) branches

The proved E₄, S₄ and A₄ component stabilizers feed the original central
SL₂ cover. The relative Sylow-centralizer condition places a faithful Q₈
in the action of C_T(u)∩L on X/O₂,Φ(X), using the same quotient maps.

Source: Aschbacher--Smith, observation following the orbit calculations in
13.1.12, printed p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL3DoubledNaturalOffenders.BinaryOrbits
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The single natural-copy stabilizer supplies the source local Q₈ action. -/
theorem NaturalMarking.selected_quaternion_action (d : NaturalMarking L)
    (h : SourceCentralizerStructure.Elimination.Context T L p)
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
      (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
      Function.Injective f := by
  have hz : (d.coordinates u).toAdd ≠ 0 := by
    intro hz
    exact hu (d.coordinates.injective (Multiplicative.toAdd.injective (by simpa using hz)))
  exact (radical_actions_of_component_symmetric_four h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides u hlocal ⟨d.movedCentralizerEquivSymmetric u hz⟩).2.2

/-- Both doubled-natural stabilizers give the source local Q₈ subgroup,
on the literal intersection C_T(u)∩L and the original odd Frattini plane. -/
theorem DoubledNaturalMarking.selected_quaternion_action (d : DoubledNaturalMarking T L)
    (h : SourceCentralizerStructure.Elimination.Context T L p)
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
      (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
      Function.Injective f := by
  by_cases hi : (d.coordinates u).toAdd ∈ independent
  · let e := d.independentCentralizerEquiv u hi
    have hc : Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L)) = 4 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
      decide
    have hs : ∀ a : (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L)), a ^ 2 = 1 := by
      intro a
      apply e.injective
      rw [map_pow,map_one]
      exact (by decide : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1) _
    exact (radical_actions_of_component_four_group h.hypothesis h.many h.maximal
      h.nonquasisimple h.odd h.divides u hlocal hc hs).2.2
  · have hz : (d.coordinates u).toAdd ≠ 0 := by
      intro hz
      exact hu (d.coordinates.injective (Multiplicative.toAdd.injective (by simpa using hz)))
    exact (radical_actions_of_component_symmetric_four h.hypothesis h.many h.maximal
      h.nonquasisimple h.odd h.divides u hlocal ⟨d.dependentCentralizerEquiv u hz hi⟩).2.2

/-- The noncentral rank-four branch has the source local Q₈ action. -/
theorem RankFourMarking.selected_quaternion_action (d : RankFourMarking L)
    (h : SourceCentralizerStructure.Elimination.Context T L p)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
      (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
      Function.Injective f := by
  have hz : d.projection (d.coordinates u).toAdd ≠ 0 :=
    fun hz => hnt (h.sylow_normalizes.trans (d.fixed_centralizer u hz))
  exact (radical_actions_of_component_alternating_four h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides u hlocal ⟨d.movedCentralizerEquivAlternating u hz⟩).2.2

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
