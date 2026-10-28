module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Orbitals
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.PlaneNeighbors
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction.Ternary
/-!
# Applying the relation reduction to the ambient coset graph

All four actual stages satisfy B1, including the proved δ₃ symmetry.
`hypothesisB` identifies the exact remaining B2 and B3 geometric statements
with the conditional graph theorem (1.4). The resulting theorem supplies the
base of the same uniqueness system, using its proved local triangle orbits.
Neither B2 nor B3 has been added to the earlier-source `Input` record. Their
section 7 proofs, and hence `source_isBase` with only `Input`, remain open.

Source: AS91 (1.4), opening of §7, and (7.9), pp.591–592,603–605.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

theorem ternary_symm (i : Fin 4) {x u y : Point d.P} (ht : d.ternary i x u y) :
    d.ternary i y u x := by
  fin_cases i
  · exact d.ternary_zero_symm ht
  · exact d.ternary_one_symm ht
  · exact d.ternary_two_symm ht
  · exact d.ternary_three_symm ht

theorem ternary_mono {i j : Fin 4} (hij : i ≤ j) {x u y : Point d.P}
    (ht : d.ternary i x u y) : d.ternary j x u y := by
  fin_cases i <;> fin_cases j <;>
    first | exact ht | exact d.ternary_zero_le_one ht |
      exact d.ternary_one_le_two ht | exact d.ternary_two_le_three ht |
      exact d.ternary_one_le_two (d.ternary_zero_le_one ht) |
      exact d.ternary_two_le_three (d.ternary_one_le_two ht) |
      exact d.ternary_two_le_three (d.ternary_one_le_two (d.ternary_zero_le_one ht)) |
      exact False.elim (by have := hij; norm_num [Fin.le_def] at this)

/-- Extend the four source stages constantly past the final stage. -/
def stage (i : ℕ) : Fin 4 := ⟨min i 3, by omega⟩

def chain (i : ℕ) := d.ternary (stage i)

/-- The still-undischarged B2 geometry, on the literal source components.
This is a separate proposition, never an earlier-source Input field. -/
def Bridge : Prop :=
  ∀ k, k < 3 → ∀ x u y v z,
    d.chain (k + 1) x u y → ¬ RelationReduction.Near (graph d.L) x y →
    Adj d.L x v → Adj d.L v z → ¬ RelationReduction.Near (graph d.L) x z →
    ∃ w q, w ∈ d.neighborhoodExtension (stage k) x u y ∧
      q ∈ commonComponent (graph d.L) x v z ∧
        RelationReduction.induced (Γ := graph d.L) d.chain (min k 1) w q

/-- The remaining geometric B3 assertion, with the exact distance-two
restrictions and the source Δ₁² pair. -/
def TripleNeighbor : Prop := ∀ x y w, PlaneDistanceTwo d.L x y →
  Adj d.L y w → DistanceTwo d.L x w →
    ∃ c, Adj d.L x c ∧ Adj d.L y c ∧ RelationReduction.Near (graph d.L) c w

theorem properTwo_iff (x y : Point d.P) :
    RelationReduction.ProperTwo (graph d.L) x y ↔ DistanceTwo d.L x y := by
  constructor
  · rintro ⟨hn, hc⟩
    exact ⟨fun he => hn (Or.inl he), fun ha => hn (Or.inr ha), hc⟩
  · rintro ⟨hne, hna, hc⟩
    exact ⟨fun hh => hh.elim hne hna, hc⟩

/-- Verification of B1 and exact identification of the remaining source
premises for the already-proved (1.4) reduction. -/
def hypothesisB (bridge : d.Bridge) (triple : d.TripleNeighbor) :
    RelationReduction.HypothesisB (graph d.L) 3 where
  ternary := d.chain
  symm := fun i _ _ _ ht => d.ternary_symm (stage i) ht
  mono := by
    intro i j hij x u y ht
    exact d.ternary_mono (show stage i ≤ stage j from min_le_min_right 3 hij) ht
  zero := fun _ _ _ => Iff.rfl
  bounded := fun _ _ _ _ ht => ⟨ht.1, ht.2.1⟩
  full := fun _ _ _ hx hy => ⟨hx, hy, trivial⟩
  bridge := by
    intro k hk x u y v z ht hn hxv hvz hnz
    exact bridge k hk x u y v z ht hn hxv hvz hnz
  triple := by
    intro x y w hrel hxy hyw hxw
    have hd := (d.properTwo_iff x y).mp hxy
    have hp : PlaneDistanceTwo d.L x y := by
      obtain hn | ⟨u, hu⟩ := hrel
      · exact (hxy.1 hn).elim
      · exact (d.binary_one_iff_planeDistanceTwo hd).mp ⟨u, hu⟩
    exact triple x y w hp hyw ((d.properTwo_iff x w).mp hxw)

/-- All graph-combinatorial contraction has been proved; the actual B2 and
B3 geometry remains explicit pending section 7's incidence calculations. -/
theorem triangulable_of_relation_conditions (bridge : d.Bridge) (triple : d.TripleNeighbor) :
    WalkClosure.Triangulable d.system.graph := by
  rw [d.system_graph]
  exact (d.hypothesisB bridge triple).triangulable

/-- The ambient uniqueness-system base under the two remaining section 7
conditions. This is not yet `source_isBase : Input h → U.IsBase`. -/
theorem isBase_of_relation_conditions (bridge : d.Bridge) (triple : d.TripleNeighbor) :
    d.system.IsBase :=
  d.isBase_of_triangulable (d.triangulable_of_relation_conditions bridge triple)

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
