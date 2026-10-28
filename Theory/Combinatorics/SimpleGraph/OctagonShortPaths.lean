module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Short paths and chord-free apartments in graphs of girth at least sixteen

A first repeated vertex of a nonbacktracking walk produces a simple cycle.
Thus walks shorter than sixteen are paths. Two paths whose lengths sum to
less than sixteen coincide. Rotating a sixteen-cycle supplies an arc of
length at most eight between any two support vertices; comparing it with
an edge excludes all chords. Its induced support therefore has two neighbors
at each vertex. These are the graph facts for the octagonal BN-pair action
in Aschbacher–Smith F.4.8.
-/

public section
namespace SimpleGraph.OctagonShortPaths
open Walk
variable {V : Type*} {G : SimpleGraph V}

/-- Girth excludes repetitions in a short nonbacktracking walk. -/
theorem isPath_of_nonbacktracking
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {n : ℕ} {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) (hn : n < 16) :
    p.toWalk.IsPath := by
  classical
  induction n generalizing x with
  | zero => exact Walk.IsPath.nil
  | succ n ih =>
    have ht : p.2.Nonbacktracking := by
      cases n with
      | zero => trivial
      | succ n => exact hp.2
    have htpath := ih p.2 ht (by omega)
    apply (Walk.cons_isPath_iff p.1.property p.2.toWalk).mpr
    refine ⟨htpath, ?_⟩
    intro hx
    cases n with
    | zero =>
      have he : x = (p.1 : V) := by
        rw [BasedWalk.support_toWalk] at hx
        exact List.mem_singleton.mp hx
      exact p.1.property.ne he
    | succ n =>
      let r := p.2.toWalk.takeUntil x hx
      have hr : r.IsPath := htpath.takeUntil hx
      have he : s(x, (p.1 : V)) ∉ r.edges := by
        intro he
        have hl : r.length = 1 := hr.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
        have hs : r.snd = x := by
          change r.getVert 1 = x
          simpa only [hl] using r.getVert_length
        have hs' : r.snd = (p.2.1 : V) := by
          have hbase : p.2.toWalk.snd = (p.2.1 : V) :=
            (Walk.getVert_cons_succ (n := 0) p.2.2.toWalk p.2.1.property).trans
              (Walk.getVert_zero _)
          exact (Walk.snd_takeUntil p.1.property.ne p.2.toWalk hx).trans hbase
        exact hp.1 (hs'.symm.trans hs)
      have hc : (Walk.cons p.1.property r).IsCycle := (Walk.cons_isCycle_iff r _).mpr ⟨hr, he⟩
      have hbound := hg x _ hc
      have hlen := p.2.toWalk.length_takeUntil_le_length hx
      rw [BasedWalk.length_toWalk] at hlen
      change 16 ≤ r.length + 1 at hbound
      change r.length ≤ n + 1 at hlen
      omega

/-- Two short paths with the same endpoints coincide. -/
theorem paths_eq
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 16) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, c, hc, hle⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have h := hg w c hc
  omega

/-- Between two vertices of a sixteen-loop there is an arc of length at most eight. -/
theorem short_arc {a u v : V} (c : G.Walk a a) (hlen : c.length = 16)
    (hu : u ∈ c.support) (hv : v ∈ c.support) :
    ∃ q : G.Walk u v, q.length ≤ 8 ∧ q.support ⊆ c.support ∧ q.edges ⊆ c.edges := by
  classical
  let r := c.rotate u hu
  have hv' : v ∈ r.support := (c.mem_support_rotate_iff u hu).mpr hv
  have hs : r.support ⊆ c.support := fun _ h => (c.mem_support_rotate_iff u hu).mp h
  have he : r.edges ⊆ c.edges := (c.rotate_edges u hu).perm.subset
  have hsum : (r.takeUntil v hv').length + (r.dropUntil v hv').length = 16 := by
    rw [← Walk.length_append, r.take_spec hv']
    simpa only [r, Walk.length_rotate] using hlen
  by_cases hshort : (r.takeUntil v hv').length ≤ 8
  · exact ⟨r.takeUntil v hv', hshort,
      fun _ h => hs (r.support_takeUntil_subset_support hv' h),
      fun _ h => he (r.edges_takeUntil_subset_edges hv' h)⟩
  · refine ⟨(r.dropUntil v hv').reverse, ?_, ?_, ?_⟩
    · rw [Walk.length_reverse]; omega
    · intro w hw
      apply hs
      apply r.support_dropUntil_subset_support hv'
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    · intro e he'
      apply he
      apply r.edges_dropUntil_subset_edges hv'
      simpa only [Walk.edges_reverse, List.mem_reverse] using he'

/-- A path of length at most seven joining two apartment vertices lies in the apartment. -/
theorem short_path_support_subset
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {a u v : V} (c : G.Walk a a) (hc : c.length = 16)
    {p : G.Walk u v} (hp : p.IsPath) (hlen : p.length ≤ 7)
    (hu : u ∈ c.support) (hv : v ∈ c.support) : p.support ⊆ c.support := by
  classical
  obtain ⟨q, hq, hqs, _⟩ := short_arc c hc hu hv
  have he : p = q.bypass := paths_eq hg hp q.bypass_isPath (by
    have hh := q.length_bypass_le_length
    omega)
  rw [he]
  exact fun _ h => hqs (q.support_bypass_subset_support h)

/-- Girth sixteen excludes every chord of a sixteen-loop. -/
theorem chordless
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {a : V} (c : G.Walk a a) (hc : c.length = 16) : c.IsChordless := by
  classical
  apply Walk.isChordless_iff_forall_mem_edges.mpr
  intro u v hu hv huv
  obtain ⟨q, hq, _, hqe⟩ := short_arc c hc hu hv
  have he : huv.toWalk = q.bypass := paths_eq hg huv.isPath_toWalk q.bypass_isPath (by
    have hh := q.length_bypass_le_length
    simp only [Adj.length_toWalk]
    omega)
  have hmem : s(u, v) ∈ q.bypass.edges := by rw [← he]; simp
  exact hqe (q.edges_bypass_subset_edges hmem)

/-- The induced support of a simple sixteen-cycle has exactly two neighbors at each vertex. -/
theorem cycle_neighbors_two
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hlen : c.length = 16)
    (v : V) (hv : v ∈ c.support) :
    {w | w ∈ c.support ∧ G.Adj v w}.ncard = 2 := by
  have hind := (Walk.isInduced_toSubgraph).mpr (chordless hg c hlen)
  have he : {w | w ∈ c.support ∧ G.Adj v w} = c.toSubgraph.neighborSet v := by
    ext w
    constructor
    · rintro ⟨hw, hadj⟩
      exact hind ((c.mem_verts_toSubgraph).mpr hv) ((c.mem_verts_toSubgraph).mpr hw) hadj
    · intro hw
      exact ⟨Walk.mem_support_of_adj_toSubgraph hw.symm, c.toSubgraph.adj_sub hw⟩
  rw [he]
  exact hc.ncard_neighborSet_toSubgraph_eq_two hv

end SimpleGraph.OctagonShortPaths
