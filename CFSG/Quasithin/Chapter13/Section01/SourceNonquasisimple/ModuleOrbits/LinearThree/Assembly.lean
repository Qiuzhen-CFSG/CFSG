module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Quaternion
public import Theory.Representation.SL3DoubledNaturalOffenders.NaturalCopyOrbits

/-!
# The L₃(2) orbit branches at the classification boundary

The source sets are identified on the original U using actual equivariant
natural embeddings. For the selected rank-one case the proved quotient
surjectivity supplies the multiplicity involution and discharges the input
to uniqueness of the T-invariant natural copy.

The final theorem dispatches genuine single-natural, doubled-natural, or
fully moved central-extension markings to the literal OrbitFacts consumer.
Producing these markings is the preceding 13.1.10 classification obligation;
no orbit or stabilizer conclusion is part of that input.

Source: Aschbacher--Smith, 13.1.10 and 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL3DoubledNaturalOffenders.BinaryOrbits
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
/-- The source complement of all natural copies, on the original U. -/
theorem DoubledNaturalMarking.independent_copy_complement (d : DoubledNaturalMarking T L)
    (u : normalizerMoved L) :
    (d.coordinates u).toAdd ∈ independent ↔
      ∀ e : BinaryLinearThree.W.IntertwiningMap rho, Function.Injective e → u ∉ d.naturalCopy e := by
  change (d.coordinates u).toAdd ∈ independent ↔
    ∀ e : BinaryLinearThree.W.IntertwiningMap rho, Function.Injective e →
      (d.coordinates u).toAdd ∉ e.toLinearMap.range
  exact independent_iff_no_natural_copy _

omit [Finite G] in
/-- The source union of natural copies minus the invariant copy, on U. -/
theorem DoubledNaturalMarking.rankOne_copy_difference (d : DoubledNaturalMarking T L)
    (u : normalizerMoved L) :
    (d.coordinates u).toAdd ∈ rankOne ↔
      (∃ e : BinaryLinearThree.W.IntertwiningMap rho, Function.Injective e ∧ u ∈ d.naturalCopy e) ∧
        u ∉ d.naturalCopy diagonalEmbedding := by
  change (d.coordinates u).toAdd ∈ rankOne ↔
      (∃ e : BinaryLinearThree.W.IntertwiningMap rho, Function.Injective e ∧
        (d.coordinates u).toAdd ∈ e.toLinearMap.range) ∧
          (d.coordinates u).toAdd ∉ diagonalEmbedding.toLinearMap.range
  rw [diagonalEmbedding_range]
  exact rankOne_iff_natural_copy_not_diagonal _

/-- Selection in the rank-one branch produces the actual multiplicity involution
in the quotient of LT; no outer-action conclusion is assumed. -/
theorem DoubledNaturalMarking.selected_rankOne_outer_element (d : DoubledNaturalMarking T L)
    (u : normalizerMoved L) (hu : (d.coordinates u).toAdd ∈ rankOne)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    ∃ m, d.quotient m = (1,Equiv.swap 0 1) :=
  (d.selected_rankOne_index u hu hlocal hnt).1 _

/-- The selected rank-one branch has exactly the source T-invariant natural copy. -/
theorem DoubledNaturalMarking.selected_rankOne_unique_copy (d : DoubledNaturalMarking T L)
    (u : normalizerMoved L) (hu : (d.coordinates u).toAdd ∈ rankOne)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G))
    (e : BinaryLinearThree.W.IntertwiningMap rho) (he : Function.Injective e)
    (hi : ∀ (t : T) (v : normalizerMoved L), v ∈ d.naturalCopy e →
      action L (inclusion (le_sup_right.trans d.invariant) t) v ∈ d.naturalCopy e) :
    d.naturalCopy e = d.naturalCopy diagonalEmbedding :=
  d.unique_sylow_invariant_copy (d.selected_rankOne_index u hu hlocal hnt).1 e he hi

omit [Finite G] in
/-- The rank-four orbit statement with the literal source nonfixed condition. -/
theorem RankFourMarking.source_nonfixed_orbit (d : RankFourMarking L)
    (u : normalizerMoved L) (hu : (u : G) ∉ centralizer (L : Set G)) :
    (centralizer ({(u : G)} : Set G)).relIndex (normalizer (L : Set G)) = 14 ∧
      Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
        alternatingGroup (Fin 4)) := by
  have hp : d.projection (d.coordinates u).toAdd ≠ 0 := by
    intro hp
    apply hu
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (d.fixed_centralizer u hp (L.le_normalizer hl))
  exact ⟨d.nonfixed_centralizer_index u hp,⟨d.movedCentralizerEquivAlternating u hp⟩⟩

/-- All L₃(2) action-marked branches discharge the literal centralizer-analysis inputs. -/
theorem orbitFacts_of_marked_linear_three {p : ℕ} [Fact p.Prime]
    (h : SourceCentralizerStructure.Elimination.Context T L p)
    (hm : Nonempty (NaturalMarking L) ∨ Nonempty (DoubledNaturalMarking T L) ∨
      Nonempty (RankFourMarking L)) :
    SourceCentralizerStructure.Elimination.OrbitFacts T L p := by
  rcases hm with hn | hd | hr
  · exact (Classical.choice hn).orbitFacts h
  · exact (Classical.choice hd).orbitFacts h
  · exact (Classical.choice hr).orbitFacts h

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
