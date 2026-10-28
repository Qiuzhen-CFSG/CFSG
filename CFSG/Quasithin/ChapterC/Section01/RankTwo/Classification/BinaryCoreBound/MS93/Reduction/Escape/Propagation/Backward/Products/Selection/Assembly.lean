module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Commutators

/-!
# Assembling the two changing-edge arguments

If both generating edges fail the first bound, their intersection lines
are the same intersection with U_d: the critical commutator is central at
d by (4.3.6). This contradicts the local pencil's distinct lines.

For the second choice, a favorable edge failing the predecessor bound has
line N = [W(t),Z_c]. If a different-line edge also satisfies the first bound
but fails the second, intersecting with U_c again identifies the two lines.
Thus the different-line edge fails the first bound. Now N and R are both
central at d, so their join is central there, contradicting the nonzero
natural commutator of the second edge's span with Z_d.

The pencil and predecessor-comparison premises remain explicit proof
obligations. These conditional assemblies are not the completed source
edge choices until those two local results have been supplied.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Two actual lines in the pencil supply an edge different from any
specified line; the generation equality is retained for the chosen edge. -/
theorem PencilFacts.exists_different_line {p : Counterexample geometry} {β : Vertex R}
    (pencil : PencilFacts p β) (t : Vertex R) :
    ∃ u, Adjacent R p.a u ∧
      (stabilizer R p.a ⊓ stabilizer R u) ⊔ Z R p.a' = stabilizer R p.a ∧
      edgeLine p β u ≠ edgeLine p β t := by
  classical
  obtain ⟨u, v, hu, hgu, hv, hgv, hne⟩ := pencil.two_lines
  by_cases h : edgeLine p β u = edgeLine p β t
  · exact ⟨v, hv, hgv, fun heq => hne (h.trans heq.symm)⟩
  · exact ⟨u, hu, hgu, h⟩

variable [Finite M]

/-- A failed first bound fixes the line independently of the chosen
generating edge. The direction of the centrality deduction is (4.3.6)'s
contrapositive: failure of the bound makes R central at d. -/
theorem failed_bound_line_eq_intersection (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (bound : BoundFacts geometry)
    (β d t : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : PencilFacts p β)
    (hd : Before p.a p.a' d 4) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    edgeLine p β t = edgeDisplacement p.a β ⊓ U R d := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hlocal := backwardSpan_le_before_stabilizer p d t hd
  have hcomm := commutator_eq_edgeLine source p hb modules control edge β hβ pencil
    d t hdc (by rw [hd.1]; have := rigidity.six_lt p; omega) hat hgen _ hlocal
    (backwardSpan_commutator_le_edge source p (by have := rigidity.six_lt p; omega)
      control d t hd hat) hbad
  have hnatural : edgeLine p β t ≤ U R d := by
    rw [← hcomm]
    exact local_commutator_le_natural source d hdc _ hlocal
  have hR := critical_le_center_of_failed_bound bound p d t hd hat hgen hbad
  rw [← pencil.line_join t hat hgen]
  exact (join_inf_natural_eq source modules d hdc _ _ hnatural hR).symm

/-- The first choice (*) on p.887, conditional only on the explicit local
pencil facts. It does not assume an edge with the desired span bound. -/
theorem favorable_edge_of_pencil (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (bound : BoundFacts geometry)
    (β d : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : PencilFacts p β)
    (hd : Before p.a p.a' d 4) :
    ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R d := by
  classical
  by_contra hn
  have hbad (t : Vertex R) (ht : Adjacent R p.a t)
      (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
      ¬ backwardSpan geometry p.a t ≤ Q R d := fun h => hn ⟨t, ht, hgen, h⟩
  obtain ⟨t, u, ht, hgt, hu, hgu, hne⟩ := pencil.two_lines
  have hline_t := failed_bound_line_eq_intersection source p hb modules control edge rigidity bound
    β d t hβ pencil hd ht hgt (hbad t ht hgt)
  have hline_u := failed_bound_line_eq_intersection source p hb modules control edge rigidity bound
    β d u hβ pencil hd hu hgu (hbad u hu hgu)
  exact hne (hline_t.trans hline_u.symm)

private theorem favorable_predecessor_line (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (comparison : PredecessorComparison geometry)
    (β d t : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : PencilFacts p β)
    (hd : Before p.a p.a' d 4) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hgood : backwardSpan geometry p.a t ≤ Q R d)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t, Z R p.c⁆ = edgeLine p β t ∧
      edgeLine p β t ≤ U R p.c := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdist : (cosetGraph R).dist d p.c = 2 :=
    before_dist (geometry := geometry) hd p.before (by decide)
  have hlocal := hgood.trans (Q_le_stabilizer_of_dist_two R d p.c hdc hdist)
  have heq := commutator_eq_edgeLine source p hb modules control edge β hβ pencil
    p.c t p.before_color (by rw [p.before.1]; exact hb) hat hgen _ hlocal
    (comparison p d t hd hat hgen hgood) hbad
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact local_commutator_le_natural source p.c p.before_color _ hlocal

/-- The second choice on p.888 from the local pencil and the predecessor
comparison. All centrality and changing-edge deductions are proved here. -/
theorem predecessor_edge_of_comparisons (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (bound : BoundFacts geometry)
    (comparison : PredecessorComparison geometry)
    (β d : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : PencilFacts p β)
    (hd : Before p.a p.a' d 4) :
    ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R p.c := by
  classical
  by_contra hn
  have hbad (t : Vertex R) (ht : Adjacent R p.a t)
      (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
      ¬ backwardSpan geometry p.a t ≤ Q R p.c := fun h => hn ⟨t, ht, hgen, h⟩
  obtain ⟨t, ht, hgt, hgood⟩ := favorable_edge_of_pencil source p hb modules control edge
    rigidity bound β d hβ pencil hd
  obtain ⟨hNt, hnatural_t⟩ := favorable_predecessor_line source p hb modules control edge comparison
    β d t hβ pencil hd ht hgt hgood (hbad t ht hgt)
  have hRc : criticalCommutator p.a p.a' ≤ localCenter p.c :=
    (p.critical_le_radius_inf_start.trans inf_le_left).trans
      (radius_le_before_center source p hb initial control edge)
  have hline_t : edgeDisplacement p.a β ⊓ U R p.c = edgeLine p β t := by
    rw [← pencil.line_join t ht hgt]
    exact join_inf_natural_eq source modules p.c p.before_color _ _ hnatural_t hRc
  obtain ⟨u, hu, hgu, hne⟩ := pencil.exists_different_line t
  have hbad_ud : ¬ backwardSpan geometry p.a u ≤ Q R d := by
    intro hgood_u
    obtain ⟨_, hnatural_u⟩ := favorable_predecessor_line source p hb modules control edge comparison
      β d u hβ pencil hd hu hgu hgood_u (hbad u hu hgu)
    have hline_u : edgeDisplacement p.a β ⊓ U R p.c = edgeLine p β u := by
      rw [← pencil.line_join u hu hgu]
      exact join_inf_natural_eq source modules p.c p.before_color _ _ hnatural_u hRc
    exact hne (hline_u.symm.trans hline_t)
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hRd := critical_le_center_of_failed_bound bound p d u hd hu hgu hbad_ud
  have hZc : Z R p.c ≤ V R d := by
    apply le_iSup_of_le p.c
    apply le_iSup_of_le (show (cosetGraph R).dist p.c d ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm, before_dist (geometry := geometry) hd p.before (by decide)]
  have hNcentral : edgeLine p β t ≤ localCenter d := by
    rw [← hNt]
    apply (commutator_mono hgood hZc).trans
    rw [commutator_comm]
    exact radius_kernel_commutator_le_center source p hb control edge d hdc
  have hplane : edgeDisplacement p.a β ≤ localCenter d := by
    rw [← pencil.line_join t ht hgt]
    exact sup_le hNcentral hRd
  have hlocal := backwardSpan_le_before_stabilizer p d u hd
  have hNu := commutator_eq_edgeLine source p hb modules control edge β hβ pencil d u hdc
    (by rw [hd.1]; have := rigidity.six_lt p; omega) hu hgu _ hlocal
    (backwardSpan_commutator_le_edge source p (by have := rigidity.six_lt p; omega)
      control d u hd hu) hbad_ud
  apply backwardSpan_commutator_not_le_center source modules p d u hd hbad_ud
  rw [hNu]
  exact (le_sup_left.trans (pencil.line_join u hu hgu).le).trans hplane

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
