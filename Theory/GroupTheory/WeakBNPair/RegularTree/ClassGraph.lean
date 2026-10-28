module
public import Theory.GroupTheory.WeakBNPair.RegularTree.QuotientAction
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The raw graph of separated equivalence classes

Vertices are the literal equivalence classes and edges have adjacent original
representatives. Neighbor lifting and separation make the quotient locally
bijective. Walks lift with their lengths and every vertex class retained.
For a tree, two short quotient paths lift to paths ending at nearby equivalent
vertices; separation identifies their endpoints and acyclicity identifies the
paths. Bounded representatives give bounded quotient walks. A path at the
separation radius with related endpoints descends to a simple cycle.

These conclusions concern the raw class graph and do not require a BN-pair
or identify the classes with orbits of the original group's action kernel.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, the generalized polygon laws in (3.6), printed pp.77--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} (Γ : SimpleGraph V) (r : Setoid V)

/-- The source graph on raw equivalence classes, with adjacency witnessed by
adjacent representatives and with loops excluded. -/
def classGraph : SimpleGraph (Quotient r) where
  Adj A B := A ≠ B ∧ ∃ a b, Quotient.mk r a = A ∧ Quotient.mk r b = B ∧ Γ.Adj a b
  symm := ⟨by
    rintro A B ⟨hne, a, b, ha, hb, hab⟩
    exact ⟨hne.symm, b, a, hb, ha, hab.symm⟩⟩
  loopless := ⟨fun A h => h.1 rfl⟩

/-- The precise local lifting condition on the underlying relation. -/
def NeighborLifting : Prop :=
  ∀ {a b c}, r a b → Γ.Adj b c → ∃ d, Γ.Adj a d ∧ r c d

variable {Γ r} {m : ℕ}

/-- Separation prevents adjacent vertices being collapsed. -/
abbrev classGraphMap (hsep : Separated r Γ m) (hm : 1 < m) : Γ →g classGraph Γ r where
  toFun := Quotient.mk r
  map_rel' := by
    intro a b hab
    refine ⟨?_, a, b, rfl, rfl, hab⟩
    intro he
    exact hab.ne (hsep (Quotient.exact he) (by rw [dist_eq_one_iff_adj.mpr hab]; exact hm))

@[simp] theorem classGraphMap_apply (hsep : Separated r Γ m) (hm : 1 < m) (a : V) :
    classGraphMap hsep hm a = Quotient.mk r a := rfl

/-- Each class neighbor has a representative at any chosen vertex in the class. -/
theorem classGraph_neighbor_lift (hlift : NeighborLifting Γ r)
    {a : V} {B : Quotient r} (hB : (classGraph Γ r).Adj (Quotient.mk r a) B) :
    ∃ b, Γ.Adj a b ∧ Quotient.mk r b = B := by
  obtain ⟨_, u, v, hu, hv, huv⟩ := hB
  obtain ⟨b, hab, hvb⟩ := hlift (r.symm (Quotient.exact hu)) huv
  exact ⟨b, hab, (Quotient.sound (r.symm hvb)).trans hv⟩

/-- Separation at distance two gives uniqueness in every neighbor fiber. -/
theorem classGraph_neighbor_bijective (hconn : Γ.Connected)
    (hsep : Separated r Γ m) (hm : 2 < m) (hlift : NeighborLifting Γ r) (a : V) :
    Function.Bijective ((classGraphMap hsep (by omega)).mapNeighborSet a) := by
  constructor
  · intro b c he
    apply Subtype.ext
    apply hsep (Quotient.exact (congrArg Subtype.val he))
    have hd := hconn.dist_triangle (u := b.val) (v := a) (w := c.val)
    rw [dist_eq_one_iff_adj.mpr b.property.symm, dist_eq_one_iff_adj.mpr c.property] at hd
    omega
  · intro B
    obtain ⟨b, hab, hb⟩ := classGraph_neighbor_lift hlift B.property
    exact ⟨⟨b, hab⟩, Subtype.ext hb⟩

/-- Lift an entire quotient walk from a specified representative, retaining
every vertex class and the literal length. -/
theorem classGraph_walk_lift (hlift : NeighborLifting Γ r)
    {A B : Quotient r} (p : (classGraph Γ r).Walk A B) (a : V)
    (ha : Quotient.mk r a = A) :
    ∃ b, ∃ q : Γ.Walk a b, Quotient.mk r b = B ∧ q.length = p.length ∧
      ∀ k, Quotient.mk r (q.getVert k) = p.getVert k := by
  induction p generalizing a with
  | nil => exact ⟨a, .nil, ha, rfl, fun k => ha⟩
  | @cons A C B hAC p ih =>
    obtain ⟨c, hac, hc⟩ := classGraph_neighbor_lift hlift (ha ▸ hAC)
    obtain ⟨b, q, hb, hlen, hverts⟩ := ih c hc
    refine ⟨b, .cons hac q, hb, by simp only [length_cons, hlen], ?_⟩
    intro k
    cases k with
    | zero => simpa only [getVert_zero] using ha
    | succ k => simpa only [getVert_cons_succ] using hverts k

/-- A lift of a path is a path: equality of two lifted vertices would give
an equality at the same two positions downstairs. -/
theorem classGraph_path_lift (hlift : NeighborLifting Γ r)
    {A B : Quotient r} (p : (classGraph Γ r).Walk A B) (hp : p.IsPath)
    (a : V) (ha : Quotient.mk r a = A) :
    ∃ b, ∃ q : Γ.Walk a b, q.IsPath ∧ Quotient.mk r b = B ∧ q.length = p.length ∧
      ∀ k, Quotient.mk r (q.getVert k) = p.getVert k := by
  obtain ⟨b, q, hb, hlen, hverts⟩ := classGraph_walk_lift hlift p a ha
  refine ⟨b, q, ?_, hb, hlen, hverts⟩
  apply (IsPath.getVert_injOn_iff q).mp
  intro i hi j hj hij
  apply hp.getVert_injOn (by simpa only [← hlen] using hi) (by simpa only [← hlen] using hj)
  rw [← hverts i, ← hverts j, hij]

/-- Short quotient paths lift to paths with nearby equivalent endpoints;
separation makes those endpoints equal and the tree makes their paths equal. -/
theorem classGraph_short_paths_unique (ht : Γ.IsTree) (hsep : Separated r Γ m)
    (hlift : NeighborLifting Γ r) {A B : Quotient r}
    (p q : (classGraph Γ r).Walk A B) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < m) : p = q := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep A
  obtain ⟨b, u, hu, hb, hul, huv⟩ := classGraph_path_lift hlift p hp a rfl
  obtain ⟨c, v, hv, hc, hvl, hvv⟩ := classGraph_path_lift hlift q hq a rfl
  have hbc : b = c := by
    apply hsep (Quotient.exact (hb.trans hc.symm))
    have hd := dist_le (u.reverse.append v)
    rw [length_append, length_reverse, hul, hvl] at hd
    omega
  subst c
  have he : u = v := congrArg Subtype.val
    (ht.isAcyclic.subsingleton_path a b |>.elim ⟨u, hu⟩ ⟨v, hv⟩)
  apply ext_getVert
  intro k
  rw [← huv k, ← hvv k, he]

/-- Bounded representatives give the diameter bound on the actual class graph. -/
theorem classGraph_bounded_walks (hconn : Γ.Connected)
    (hsep : Separated r Γ m) (hm : 1 < m) (n : ℕ)
    (hbound : ∀ a x, ∃ y, r x y ∧ Γ.dist a y ≤ n)
    (A B : Quotient r) : ∃ p : (classGraph Γ r).Walk A B, p.length ≤ n := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep A
  obtain ⟨b, rfl⟩ := Quotient.exists_rep B
  obtain ⟨c, hbc, hc⟩ := hbound a b
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a c
  exact ⟨(p.map (classGraphMap hsep hm)).copy rfl (Quotient.sound (r.symm hbc)),
    by simpa only [length_copy, length_map, hp] using hc⟩

private theorem dist_getVert_le_length {a b : V} (p : Γ.Walk a b) (i j : ℕ) :
    Γ.dist (p.getVert i) (p.getVert j) ≤ p.length := by
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm]
    exact this j i (by omega)
  have hd := dist_le ((p.take j).drop i)
  simp only [take_getVert, min_eq_right hij, drop_length, take_length] at hd
  omega

/-- A path shorter than the separation radius maps to a path. -/
theorem classGraph_map_short_path (hsep : Separated r Γ m) (hm : 1 < m)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length < m) :
    (p.map (classGraphMap hsep hm)).IsPath := by
  apply (IsPath.getVert_injOn_iff _).mp
  intro i hi j hj hij
  simp only [length_map] at hi hj
  apply hp.getVert_injOn hi hj
  simp only [getVert_map, classGraphMap_apply] at hij
  apply hsep (Quotient.exact hij)
  exact lt_of_le_of_lt (dist_getVert_le_length p i j) hlen

/-- A path of the separation length with equivalent endpoints closes to a
simple cycle in the raw quotient, without a group-kernel lifting premise. -/
theorem classGraph_cycle_of_path (hsep : Separated r Γ m) (hm : 2 < m)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = m) (hab : r b a) :
    ∃ q : (classGraph Γ r).Walk (Quotient.mk r a) (Quotient.mk r a),
      q.IsCycle ∧ q.length = m := by
  cases p with
  | nil => simp only [length_nil] at hlen; omega
  | @cons a c b hac p =>
    have hpl : p.length + 1 = m := hlen
    let f := classGraphMap hsep (by omega : 1 < m)
    let q : (classGraph Γ r).Walk (Quotient.mk r c) (Quotient.mk r a) :=
      (p.map f).copy rfl (Quotient.sound hab)
    have hq : q.IsPath := by
      dsimp only [q]
      rw [isPath_copy]
      exact classGraph_map_short_path hsep (by omega) p hp.of_cons (by omega)
    refine ⟨.cons (f.map_adj hac) q, (cons_isCycle_iff _ _).mpr ⟨hq, ?_⟩, ?_⟩
    · intro he
      have he' : s(Quotient.mk r c, Quotient.mk r a) ∈ q.edges := by
        simpa only [f, classGraphMap_apply, Sym2.eq_swap] using he
      have h1 := hq.length_eq_one_of_mem_edges he'
      simp only [q, length_copy, length_map] at h1
      omega
    · simp only [length_cons, q, length_copy, length_map, hpl]

end Theory.GroupTheory.WeakBNPair.RegularTree
