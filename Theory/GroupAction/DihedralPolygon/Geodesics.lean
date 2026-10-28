module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Short geodesics and immersed polygon circuits

In a bipartite graph with a unique geodesic between every pair at distance
less than `m`, every nonbacktracking walk of length at most `m` is geodesic.
A positive return in a nonbacktracking sequence therefore takes at least
`2*m` steps. At that minimum period, the sequence is an induced embedding
of the standard cycle graph, with exactly the sequence's vertex set.

The geodesic proof inducts on the first edge: parity excludes an unchanged
distance, and a shorter distance would produce a second short geodesic,
forcing an immediate reversal. Comparing the two arcs proves the return
bound and excludes chords.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of F.3.6, printed p.272. The assumption here
is uniqueness at EVERY distance less than `m`; uniqueness only at distance
`m-1`, as printed, is insufficient without further ambient hypotheses.
-/

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

/-- Any two distance-minimizing walks of length less than `m` coincide. -/
def UniqueGeodesicsBelow (Γ : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ ⦃x y : V⦄ (p q : Γ.Walk x y),
    p.length = Γ.dist x y → q.length = Γ.dist x y → Γ.dist x y < m → p = q

namespace Walk

/-- No pair of consecutive edges immediately returns to its initial vertex. -/
def Nonbacktracking {x y : V} (p : Γ.Walk x y) : Prop :=
  ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

theorem Nonbacktracking.tail_cons {x y z : V} {h : Γ.Adj x y} {p : Γ.Walk y z}
    (hp : (p.cons h).Nonbacktracking) : p.Nonbacktracking := by
  intro i hi
  simpa only [getVert_cons_succ, Nat.add_assoc] using hp (i + 1) (by simp only [length_cons]; omega)

end Walk

private theorem walk_color_iff (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    {x y : V} (p : Γ.Walk x y) : color x = color y ↔ p.length % 2 = 0 := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hcol := hc h
    simp only [Walk.length_cons]
    cases hx : color x <;> cases hy : color y <;> cases hz : color z <;>
      simp_all <;> omega

private theorem dist_color_iff (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    {x y : V} (h : Γ.Reachable x y) : color x = color y ↔ Γ.dist x y % 2 = 0 := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact walk_color_iff color hc p

theorem Walk.Nonbacktracking.length_eq_dist {m : ℕ}
    (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    {x y : V} {p : Γ.Walk x y} (hp : p.Nonbacktracking) (hl : p.length ≤ m) :
    p.length = Γ.dist x y := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have ht := hp.tail_cons
    have hlen : p.length = Γ.dist y z := ih ht (by simp only [Walk.length_cons] at hl; omega)
    by_cases heq : Γ.dist x z = Γ.dist y z
    · have hx := (dist_color_iff color hc (p.cons h).reachable)
      have hy := (dist_color_iff color hc p.reachable)
      have hxy := hc h
      rw [heq] at hx
      cases ha : color x <;> cases hb : color y <;> cases hz : color z <;> simp_all
    · have hd := h.symm.diff_dist_adj (u := z)
      rw [dist_comm (u := z) (v := x), dist_comm (u := z) (v := y)] at hd
      rcases hd with hd | hd | hd
      · exact (heq hd).elim
      · simpa only [Walk.length_cons, hlen] using hd.symm
      · obtain ⟨q, hq⟩ := (p.cons h).reachable.exists_walk_length_eq_dist
        have hn : 0 < p.length := by
          by_contra hh
          have hn : p.length = 0 := by omega
          have hz : y = z := p.eq_of_length_eq_zero hn
          subst z
          have hdx : Γ.dist x y = 1 := dist_eq_one_iff_adj.mpr h
          simp_all
        have hqq : (q.cons h.symm).length = Γ.dist y z := by
          simp only [Walk.length_cons, hq]; omega
        have hpq : p = q.cons h.symm := hu p (q.cons h.symm) hlen hqq (by
          simp only [Walk.length_cons] at hl; omega)
        have hnb := hp 0 (by simp only [Walk.length_cons]; omega)
        have hfirst := congrArg (fun w : Γ.Walk y z => w.getVert 1) hpq
        simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at hfirst
        apply False.elim
        apply hnb
        simpa only [Walk.getVert_zero, show 2 = 1 + 1 from rfl, Walk.getVert_cons_succ] using hfirst.symm

end SimpleGraph
namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

/-- The walk along an indexed sequence of adjacent vertices. -/
def chainWalk (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (i : ℕ) : (n : ℕ) → Γ.Walk (v i) (v (i + n))
  | 0 => .nil
  | n + 1 => ((chainWalk v hadj (i + 1) n).cons (hadj i)).copy rfl (by congr 1; omega)

@[simp] theorem length_chainWalk (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (i n : ℕ) : (chainWalk v hadj i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [chainWalk, Walk.length_copy, Walk.length_cons, ih]

theorem getVert_chainWalk (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (i n k : ℕ) (hk : k ≤ n) : (chainWalk v hadj i n).getVert k = v (i + k) := by
  induction n generalizing i k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [chainWalk, Walk.getVert_copy, Walk.getVert_cons_succ]
      rw [ih (i + 1) k (by omega)]
      congr 1
      omega

theorem chainWalk_nonbacktracking (v : ℕ → V)
    (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (i n : ℕ) :
    (chainWalk v hadj i n).Nonbacktracking := by
  intro k hk
  rw [length_chainWalk] at hk
  rw [getVert_chainWalk v hadj i n k (by omega),
    getVert_chainWalk v hadj i n (k + 2) hk, ← Nat.add_assoc]
  exact hnb (i + k)

/-- The metric along a locally nonbacktracking sequence, through half the girth. -/
theorem chain_dist {m : ℕ} (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (i n : ℕ) (hn : n ≤ m) :
    Γ.dist (v i) (v (i + n)) = n := by
  simpa only [length_chainWalk] using
    ((chainWalk_nonbacktracking v hadj hnb i n).length_eq_dist hu color hc (by simp; omega)).symm

/-- A positive return in a nonbacktracking sequence has length at least `2*m`. -/
theorem chain_return_bound {m : ℕ} (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (i n : ℕ) (hn : 0 < n)
    (hreturn : v (i + n) = v i) : 2 * m ≤ n := by
  by_cases hnm : n ≤ m
  · have h := chain_dist hu color hc v hadj hnb i n hnm
    rw [hreturn, dist_self] at h
    omega
  · have h := chain_dist hu color hc v hadj hnb i m le_rfl
    have hle := dist_le (chainWalk v hadj (i + m) (n - m))
    rw [length_chainWalk, show i + m + (n - m) = i + n by omega, hreturn,
      dist_comm, h] at hle
    omega

/-- At the minimum positive period the cyclic coordinates are distinct. -/
theorem chain_injective_of_lt {m : ℕ} (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) :
    Function.Injective (fun i : Fin (2 * m) => v i.val) := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := chain_return_bound hu color hc v hadj hnb i.val (j.val - i.val)
      (by omega) (by simpa only [Nat.add_sub_of_le hlt.le] using hij.symm)
    omega
  · have h := chain_return_bound hu color hc v hadj hnb j.val (i.val - j.val)
      (by omega) (by simpa only [Nat.add_sub_of_le hgt.le] using hij)
    omega

end SimpleGraph
namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

private theorem chain_adj_forward {m : ℕ} (hu : Γ.UniqueGeodesicsBelow m)
    (color : V → Bool) (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (hper : ∀ i, v (i + 2 * m) = v i)
    {i j : ℕ} (hi : i < j) (hj : j < 2 * m) (h : Γ.Adj (v i) (v j)) :
    j - i = 1 ∨ 2 * m + i - j = 1 := by
  by_cases hk : j - i ≤ m
  · have hd := chain_dist hu color hc v hadj hnb i (j - i) hk
    rw [Nat.add_sub_of_le hi.le, dist_eq_one_iff_adj.mpr h] at hd
    exact Or.inl hd.symm
  · have hd := chain_dist hu color hc v hadj hnb j (2 * m + i - j) (by omega)
    rw [show j + (2 * m + i - j) = i + 2 * m by omega, hper,
      dist_eq_one_iff_adj.mpr h.symm] at hd
    exact Or.inr hd.symm

/-- A minimum-period locally nonbacktracking circuit has exactly the cycle adjacencies. -/
theorem chain_adj_iff {m : ℕ} (_hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m)
    (color : V → Bool) (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (hper : ∀ i, v (i + 2 * m) = v i)
    (i j : Fin (2 * m)) :
    Γ.Adj (v i.val) (v j.val) ↔ (cycleGraph (2 * m)).Adj i j := by
  rw [cycleGraph_adj']
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · have hfin : i < j := hlt
    have hs : (i - j).val = 2 * m + i.val - j.val := by
      rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hs, Fin.sub_val_of_le hfin.le]
    constructor
    · intro h
      exact (chain_adj_forward hu color hc v hadj hnb hper hlt j.isLt h).symm
    · rintro (h | h)
      · have hi : i.val = 0 := by omega
        have hj : j.val + 1 = 2 * m := by omega
        have ha := hadj j.val
        have hvzero : v (2 * m) = v 0 := by simpa only [Nat.zero_add] using hper 0
        simpa only [hj, hvzero, hi] using ha.symm
      · have hj : j.val = i.val + 1 := by omega
        rw [hj]
        exact hadj i.val
  · have hij : i = j := Fin.ext heq
    subst j
    rw [Fin.sub_val_of_le le_rfl]
    simp
  · have hfin : j < i := hgt
    have hs : (j - i).val = 2 * m + j.val - i.val := by
      rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [Fin.sub_val_of_le hfin.le, hs]
    constructor
    · intro h
      exact chain_adj_forward hu color hc v hadj hnb hper hgt i.isLt h.symm
    · rintro (h | h)
      · have hi : i.val = j.val + 1 := by omega
        rw [hi]
        exact (hadj j.val).symm
      · have hj : j.val = 0 := by omega
        have hi : i.val + 1 = 2 * m := by omega
        have ha := hadj i.val
        have hvzero : v (2 * m) = v 0 := by simpa only [Nat.zero_add] using hper 0
        simpa only [hi, hvzero, hj] using ha

/-- The induced embedding of a minimum-period circuit in the ambient graph. -/
def chainCycleEmbedding {m : ℕ} (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m)
    (color : V → Bool) (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (v : ℕ → V) (hadj : ∀ i, Γ.Adj (v i) (v (i + 1)))
    (hnb : ∀ i, v i ≠ v (i + 2)) (hper : ∀ i, v (i + 2 * m) = v i) :
    cycleGraph (2 * m) ↪g Γ where
  toFun i := v i.val
  inj' := chain_injective_of_lt hu color hc v hadj hnb
  map_rel_iff' := chain_adj_iff hm hu color hc v hadj hnb hper _ _

end SimpleGraph
namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

/-- A periodic sequence of edges without immediate reversals. Vertices need not yet be distinct. -/
structure NonbacktrackingCircuit (Γ : SimpleGraph V) (length : ℕ) where
  vertex : ℕ → V
  adjacent : ∀ i, Γ.Adj (vertex i) (vertex (i + 1))
  nonbacktracking : ∀ i, vertex i ≠ vertex (i + 2)
  periodic : ∀ i, vertex (i + length) = vertex i

namespace NonbacktrackingCircuit
variable {L m : ℕ} (C : Γ.NonbacktrackingCircuit L)

include C in
/-- The girth bound forces the period of an immersed circuit to be at least `2*m`. -/
theorem length_ge (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y) (hL : 0 < L) : 2 * m ≤ L :=
  chain_return_bound hu color hc C.vertex C.adjacent C.nonbacktracking 0 L hL (C.periodic 0)

/-- At the minimum period the circuit is an induced copy of the standard cycle graph. -/
def embedding (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y) (hL : L = 2 * m) :
    cycleGraph (2 * m) ↪g Γ :=
  chainCycleEmbedding hm hu color hc C.vertex C.adjacent C.nonbacktracking
    (fun i => hL ▸ C.periodic i)

theorem vertex_mod (i : ℕ) : C.vertex (i % L) = C.vertex i := by
  have h (a k : ℕ) : C.vertex (a + k * L) = C.vertex a := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, ← Nat.add_assoc, C.periodic, ih]
  have hi : i % L + (i / L) * L = i := by simpa only [Nat.mul_comm] using Nat.mod_add_div i L
  simpa only [hi] using (h (i % L) (i / L)).symm

/-- The embedded cycle has precisely the vertices of the original periodic sequence. -/
theorem range_embedding (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m)
    (color : V → Bool) (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (hL : L = 2 * m) :
    Set.range (C.embedding hm hu color hc hL) = Set.range C.vertex := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩
  · rintro ⟨i, rfl⟩
    have hpos : 0 < L := by omega
    exact ⟨⟨i % L, hL ▸ Nat.mod_lt i hpos⟩, C.vertex_mod i⟩

end NonbacktrackingCircuit
end SimpleGraph
namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

/-- Taking an initial segment preserves the absence of backtracking. -/
theorem Walk.Nonbacktracking.take {x y : V} {p : Γ.Walk x y}
    (hp : p.Nonbacktracking) (n : ℕ) : (p.take n).Nonbacktracking := by
  intro i hi
  simp only [Walk.take_length] at hi
  rw [Walk.take_getVert, Walk.take_getVert,
    Nat.min_eq_right (by omega : i ≤ n), Nat.min_eq_right (by omega : i + 2 ≤ n)]
  exact hp i (by omega)

/-- A simple cycle has no immediate reversal. -/
theorem Walk.IsCycle.nonbacktracking {x : V} {p : Γ.Walk x x}
    (hp : p.IsCycle) : p.Nonbacktracking := by
  intro i hi
  simpa only [Nat.add_sub_cancel] using
    hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)

/-- Short geodesic uniqueness in a bipartite graph excludes every shorter cycle. -/
theorem Walk.IsCycle.length_ge_of_uniqueGeodesicsBelow {m : ℕ}
    (hu : Γ.UniqueGeodesicsBelow m) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    {x : V} {p : Γ.Walk x x} (hp : p.IsCycle) : 2 * m ≤ p.length := by
  have hpnb := hp.nonbacktracking
  by_cases hlen : p.length ≤ m
  · have h := hpnb.length_eq_dist hu color hc hlen
    have hpos := hp.three_le_length
    rw [dist_self] at h
    omega
  · have hm : m ≤ p.length := by omega
    have hd := (hpnb.take m).length_eq_dist hu color hc (by simp only [Walk.take_length]; omega)
    rw [Walk.take_length, Nat.min_eq_left hm] at hd
    have hbound := dist_le (p.drop m)
    rw [Walk.drop_length, dist_comm, ← hd] at hbound
    omega

end SimpleGraph
