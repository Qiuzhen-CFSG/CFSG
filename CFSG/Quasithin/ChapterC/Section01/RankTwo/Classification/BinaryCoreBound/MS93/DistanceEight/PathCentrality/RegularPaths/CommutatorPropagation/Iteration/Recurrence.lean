module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Transport

/-!
# The backward four-step induction and its two terminal indices

The natural-module edge-switching implication is kept explicit. Two regular
turns then propagate the subgroup by four edges. Induction gives the exact
source recurrence and ends at index zero or two according to the even
critical distance modulo four. At zero the seed contradicts containment
in Z_a; at two it lies in the required natural summand.

Source: Meierfrankenfeld--Stellmacher (1993), the recurrence in (4.4.4),
printed p.894. No constructor of BackwardEdgeSwitching is asserted here.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The local edge identification still to be supplied by the natural-module
argument. It is separate from the geometric recurrence and is not asserted here. -/
def BackwardEdgeSwitching {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (K : Subgroup (FreeAmalgam R)) : Prop :=
  ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) →
    K ≤ fixedCore R (p.walk.getVert (p.walk.length - 4 * n + 2)) →
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n - 1))

private theorem path_adj {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i : ℕ} (hi : i < p.walk.length) :
    Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ hi)

/-- Two successive regular turns propagate one edge identification four
positions backward, preserving the intermediate D-containment. -/
theorem four_step [Finite M] (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} {j : ℕ}
    (heven : Even j) (hj : 4 ≤ j) (hlen : j + 2 ≤ p.walk.length)
    (hforward : K = edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j + 1)))
    (hback : K = edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)))
    (hfixed : K ≤ fixedCore R (p.walk.getVert (j + 2))) :
    K ≤ fixedCore R (p.walk.getVert (j - 2)) ∧
      K = edgeCommutator R (p.walk.getVert (j - 4)) (p.walk.getVert (j - 3)) := by
  have hadj (i : ℕ) (hi : i < p.walk.length) := path_adj p hi
  have hc : color R (p.walk.getVert (j - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hcDist : (cosetGraph R).dist (p.walk.getVert j) (p.walk.getVert (j - 2)) = 2 := by
    rw [SimpleGraph.dist_comm, path_distance p (by omega) (by omega)]
    omega
  obtain ⟨g, hg, ht⟩ := hp j heven (by omega) hlen
  have hfix : K ≤ fixedCore R (p.walk.getVert (j - 2)) := by
    apply transport_fixed_of_equal_edges (geometry := geometry) hcDist (hadj j (by omega))
      (by simpa only [show j + 1 + 1 = j + 2 by omega] using hadj (j + 1) (by omega))
      (adjacent_symm R (by simpa only [show j - 1 + 1 = j by omega] using hadj (j - 1) (by omega)))
      (adjacent_symm R (by simpa only [show j - 2 + 1 = j - 1 by omega] using hadj (j - 2) (by omega)))
      hg ht hforward hback hfixed
  refine ⟨hfix, ?_⟩
  have heven' : Even (j - 2) := by rw [Nat.even_iff] at heven ⊢; omega
  obtain ⟨l, hl, ht'⟩ := hp (j - 2) heven' (by omega) (by omega)
  have hturn : Stellmacher.PushingUp.AmalgamGraph.act R l (p.walk.getVert j) =
      p.walk.getVert (j - 4) := by
    simpa only [show j - 2 + 2 = j by omega, show j - 2 - 2 = j - 4 by omega] using ht'
  apply transport_edge_of_fixed (geometry := geometry) source hc
    (by rw [SimpleGraph.dist_comm, path_distance p (by omega) (by omega)]; omega)
    (by simpa only [show j - 2 + 1 = j - 1 by omega] using hadj (j - 2) (by omega))
    (by simpa only [show j - 1 + 1 = j by omega] using hadj (j - 1) (by omega))
    (adjacent_symm R (by simpa only [show j - 3 + 1 = j - 2 by omega] using hadj (j - 3) (by omega)))
    (adjacent_symm R (by simpa only [show j - 4 + 1 = j - 3 by omega] using hadj (j - 4) (by omega)))
    hl hturn hback hfix

/-- The complete four-step induction, conditional only on its local edge
switching lemma. The final indices zero and two are both retained. -/
theorem iterate_edges [Finite M] (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hswitch : BackwardEdgeSwitching p K)
    (n : ℕ) (hn : 0 < n) (hbound : 4 * n ≤ p.walk.length) :
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n + 1)) ∧
      K ≤ fixedCore R (p.walk.getVert (p.walk.length - 4 * n + 2)) := by
  have hlenEven : Even p.walk.length := by
    rw [p.length_eq_b]
    exact geometry.even (alpha R) rfl
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        have h4 : 4 ≤ p.walk.length := by omega
        constructor
        · simpa only [Nat.zero_add, Nat.mul_one,
            show p.walk.length - 4 + 1 = p.walk.length - 3 by omega] using seed.preceding_edge
        · simpa only [Nat.zero_add, Nat.mul_one,
            show p.walk.length - 4 + 2 = p.walk.length - 2 by omega] using seed.penultimate_fixed
      have hnpos : 0 < n := by omega
      obtain ⟨hedge, hfixed⟩ := ih hnpos (by omega)
      have hj : 4 ≤ p.walk.length - 4 * n := by omega
      have heven : Even (p.walk.length - 4 * n) := by
        rw [Nat.even_iff] at hlenEven ⊢
        omega
      have hback := hswitch n hnpos (by omega) hedge hfixed
      obtain ⟨hfixed', hedge'⟩ := four_step source p hp heven hj (by omega) hedge hback hfixed
      constructor
      · simpa only [show p.walk.length - 4 * n - 4 = p.walk.length - 4 * (n + 1) by omega,
          show p.walk.length - 4 * n - 3 = p.walk.length - 4 * (n + 1) + 1 by omega] using hedge'
      · simpa only [show p.walk.length - 4 * n - 2 = p.walk.length - 4 * (n + 1) + 2 by omega] using hfixed'

/-- The literal recurrence printed in (4.4.4), including the fixed core
two positions behind each stage rather than the induction's forward core. -/
theorem source_recurrence [Finite M] (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hswitch : BackwardEdgeSwitching p K)
    (n : ℕ) (hn : 0 < n) (hbound : 4 * n < geometry.b R - 2) :
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n + 1)) ∧
      K ≤ fixedCore R (p.walk.getVert (p.walk.length - 4 * n - 2)) := by
  have hlen := p.length_eq_b
  have heven : Even (p.walk.length - 4 * n) := by
    have hh : Even p.walk.length := by
      rw [hlen]
      exact geometry.even (alpha R) rfl
    rw [Nat.even_iff] at hh ⊢
    omega
  have hj : 4 ≤ p.walk.length - 4 * n := by
    rw [Nat.even_iff] at heven
    omega
  obtain ⟨hedge, hfixed⟩ := iterate_edges source p hp seed hswitch n hn (by omega)
  have hback := hswitch n hn (by omega) hedge hfixed
  exact ⟨hedge, (four_step source p hp heven hj (by omega) hedge hback hfixed).1⟩

/-- At the last four-step stage, divisibility by four contradicts the seed;
the other even residue puts the actual subgroup in U_(a+2). -/
theorem le_second_natural_of_switching [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hswitch : BackwardEdgeSwitching p K) : K ≤ U R (p.walk.getVert 2) := by
  have hlen := p.length_eq_b
  have hlenEven : Even p.walk.length := by
    rw [hlen]
    exact geometry.even (alpha R) rfl
  have hmod : p.walk.length % 4 = 0 ∨ p.walk.length % 4 = 2 := by
    rw [Nat.even_iff] at hlenEven
    omega
  obtain ⟨hedge, _⟩ := iterate_edges source p hp seed hswitch (p.walk.length / 4)
    (by omega) (by omega)
  have heq : p.walk.length - 4 * (p.walk.length / 4) = p.walk.length % 4 := by omega
  rw [heq] at hedge
  rcases hmod with hzero | htwo
  · rw [hzero, SimpleGraph.Walk.getVert_zero] at hedge
    apply (seed.not_le_start_Z ?_).elim
    rw [hedge]
    have hadj : Adjacent R a (p.walk.getVert 1) := by
      simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using path_adj p (i := 0) (by omega)
    exact (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a _ p.start_color hadj).trans (U_le_Z R a)
  · rw [htwo] at hedge
    rw [hedge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ ((p.vertex_color (by omega)).mpr (by decide))
      (path_adj p (by omega))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
