module

public import Theory.Combinatorics.SimpleGraph.PathLifting
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Extending and truncating nonbacktracking walks

The length-indexed walks used in the covering theorem admit prefixes and terminal
extensions. A minimum valence of two allows every nonbacktracking walk to be
extended to any larger length. These operations provide the surjectivity needed
to descend path transitivity. Shortest Mathlib walks are bridged to this
presentation without identifying arbitrary nonbacktracking walks with paths.

Source: Aschbacher–Smith, Lemma F.3.5, first paragraph of the proof, p. 271.
-/

@[expose] public section

namespace SimpleGraph.BasedWalk

universe u v
variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The prefix consisting of the first `i` edges. -/
def take : {n : ℕ} → {x : V} → (i : ℕ) → i ≤ n →
    BasedWalk G n x → BasedWalk G i x
  | _, _, 0, _, _ => PUnit.unit
  | _ + 1, _, i + 1, hi, p => ⟨p.1, take i (Nat.le_of_succ_le_succ hi) p.2⟩

@[simp] theorem length_vertices {n : ℕ} {x : V} (p : BasedWalk G n x) :
    p.vertices.length = n + 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih p.2)

@[simp] theorem vertices_take {n : ℕ} {x : V} (i : ℕ) (hi : i ≤ n)
    (p : BasedWalk G n x) : (take i hi p).vertices = p.vertices.take (i + 1) := by
  induction i generalizing n x with
  | zero => cases n <;> rfl
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n => exact congrArg (List.cons x) (ih (Nat.le_of_succ_le_succ hi) p.2)

@[simp] theorem take_self {n : ℕ} {x : V} (p : BasedWalk G n x) :
    take n le_rfl p = p := by
  apply vertices_injective n x
  simp

theorem nonbacktracking_take {n i : ℕ} {x : V} (hi : i ≤ n)
    (p : BasedWalk G n x) (hp : p.Nonbacktracking) : (take i hi p).Nonbacktracking := by
  induction n generalizing x i with
  | zero =>
    have : i = 0 := by omega
    subst i
    trivial
  | succ n ih =>
    cases i with
    | zero => trivial
    | succ i =>
      cases i with
      | zero => trivial
      | succ i =>
        cases n with
        | zero => omega
        | succ n =>
          exact ⟨hp.1, ih (by omega) p.2 hp.2⟩

/-- The vertex just before the endpoint of a positive-length walk. -/
def penultimate : {n : ℕ} → {x : V} → BasedWalk G (n + 1) x → V
  | 0, x, _ => x
  | _ + 1, _, p => penultimate p.2

theorem adj_penultimate_endpoint {n : ℕ} {x : V} (p : BasedWalk G (n + 1) x) :
    G.Adj p.penultimate p.endpoint := by
  induction n generalizing x with
  | zero => exact p.1.2
  | succ n ih => exact ih p.2

/-- Append one adjacent vertex. -/
def snoc : {n : ℕ} → {x z : V} → (p : BasedWalk G n x) →
    G.Adj p.endpoint z → BasedWalk G (n + 1) x
  | 0, _, z, _, hz => ⟨⟨z, hz⟩, PUnit.unit⟩
  | _ + 1, _, _, p, hz => ⟨p.1, snoc p.2 hz⟩

@[simp] theorem endpoint_snoc {n : ℕ} {x z : V} (p : BasedWalk G n x)
    (hz : G.Adj p.endpoint z) : (p.snoc hz).endpoint = z := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2 hz

@[simp] theorem vertices_snoc {n : ℕ} {x z : V} (p : BasedWalk G n x)
    (hz : G.Adj p.endpoint z) : (p.snoc hz).vertices = p.vertices ++ [z] := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons x) (ih p.2 hz)

@[simp] theorem penultimate_snoc {n : ℕ} {x z : V} (p : BasedWalk G n x)
    (hz : G.Adj p.endpoint z) : (p.snoc hz).penultimate = p.endpoint := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2 hz

@[simp] theorem take_snoc {n : ℕ} {x z : V} (p : BasedWalk G n x)
    (hz : G.Adj p.endpoint z) : take n (Nat.le_succ n) (p.snoc hz) = p := by
  apply vertices_injective n x
  rw [vertices_take, vertices_snoc, ← length_vertices p, List.take_left]

theorem nonbacktracking_snoc_iff {n : ℕ} {x z : V}
    (p : BasedWalk G (n + 1) x) (hz : G.Adj p.endpoint z) :
    (p.snoc hz).Nonbacktracking ↔ p.Nonbacktracking ∧ z ≠ p.penultimate := by
  induction n generalizing x with
  | zero =>
    change (z ≠ x ∧ True) ↔ (True ∧ z ≠ x)
    simp
  | succ n ih =>
    change G.Adj p.2.endpoint z at hz
    have hi := and_congr (Iff.refl ((p.2.1 : V) ≠ x)) (ih p.2 hz)
    cases n with
    | zero => simp only [Nonbacktracking, snoc, penultimate, and_true]
    | succ n =>
      simpa only [Nonbacktracking, snoc, penultimate, and_true, true_and, and_assoc] using hi

/-- Valence at least two in a form that also applies to infinite neighbor sets. -/
def HasTwoNeighbors (G : SimpleGraph V) : Prop :=
  ∀ x y : V, ∃ z, G.Adj x z ∧ z ≠ y

/-- A nonbacktracking walk always has a nonbacktracking one-edge extension. -/
theorem exists_nonbacktracking_snoc (hdeg : HasTwoNeighbors G)
    {n : ℕ} {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) :
    ∃ (z : V) (hz : G.Adj p.endpoint z), (p.snoc hz).Nonbacktracking := by
  cases n with
  | zero =>
    obtain ⟨z, hz, _⟩ := hdeg x x
    exact ⟨z, hz, trivial⟩
  | succ n =>
    obtain ⟨z, hz, hne⟩ := hdeg p.endpoint p.penultimate
    exact ⟨z, hz, (nonbacktracking_snoc_iff p hz).2 ⟨hp, hne⟩⟩

theorem take_take {n i j : ℕ} {x : V} (hij : i ≤ j) (hjn : j ≤ n)
    (p : BasedWalk G n x) : take i hij (take j hjn p) = take i (hij.trans hjn) p := by
  apply vertices_injective i x
  simp [List.take_take, Nat.min_eq_left (Nat.succ_le_succ hij)]

/-- Every nonbacktracking walk extends to every larger prescribed length. -/
theorem exists_extension (hdeg : HasTwoNeighbors G) {n N : ℕ} (hn : n ≤ N)
    {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) :
    ∃ q : BasedWalk G N x, q.Nonbacktracking ∧ take n hn q = p := by
  induction N, hn using Nat.le_induction with
  | base => exact ⟨p, hp, take_self p⟩
  | succ N hn ih =>
    obtain ⟨q, hq, htake⟩ := ih
    obtain ⟨z, hz, hnb⟩ := exists_nonbacktracking_snoc hdeg q hq
    refine ⟨q.snoc hz, hnb, ?_⟩
    rw [← take_take hn (Nat.le_succ N), take_snoc, htake]

theorem getLast?_vertices {n : ℕ} {x : V} (p : BasedWalk G n x) :
    p.vertices.getLast? = some p.endpoint := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih p.2

theorem endpoint_map (f : G →g H) {n : ℕ} {x : V} (p : BasedWalk G n x) :
    (map f p).endpoint = f p.endpoint := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2

/-- Equality of vertex lists, including when their basepoints differ, determines
the endpoints. -/
theorem endpoint_eq_of_vertices_eq {n k : ℕ} {x y : V}
    (p : BasedWalk G n x) (q : BasedWalk G k y) (hpq : p.vertices = q.vertices) :
    p.endpoint = q.endpoint := by
  exact Option.some.inj (by simpa only [getLast?_vertices] using congrArg List.getLast? hpq)

/-- A simple Mathlib path has no immediate backtrack in the based presentation. -/
theorem nonbacktracking_ofWalk_of_isPath {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    (ofWalk p).Nonbacktracking := by
  induction p with
  | nil => trivial
  | @cons x z y hx p ih =>
    have h := (Walk.cons_isPath_iff hx p).1 hp
    cases p with
    | nil => trivial
    | @cons z w y hz p =>
      refine ⟨?_, ih h.1⟩
      intro heq
      apply h.2
      have hw : w ∈ (Walk.cons hz p).support := by
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr p.start_mem_support
      exact heq ▸ hw

@[simp] theorem vertices_cast {n k : ℕ} {x : V} (h : n = k)
    (p : BasedWalk G n x) : (h ▸ p).vertices = p.vertices := by
  subst k
  rfl

@[simp] theorem endpoint_cast {n k : ℕ} {x : V} (h : n = k)
    (p : BasedWalk G n x) : (h ▸ p).endpoint = p.endpoint := by
  subst k
  rfl

@[simp] theorem nonbacktracking_cast {n k : ℕ} {x : V} (h : n = k)
    (p : BasedWalk G n x) : (h ▸ p).Nonbacktracking ↔ p.Nonbacktracking := by
  subst k
  rfl

/-- A metric geodesic is nonbacktracking. -/
theorem nonbacktracking_of_geodesic {n : ℕ} {x : V}
    (p : BasedWalk G n x) (hp : G.dist x p.endpoint = n) : p.Nonbacktracking := by
  have hpath : p.toWalk.IsPath := p.toWalk.isPath_of_length_eq_dist (by
    rw [length_toWalk, hp])
  have hnb := nonbacktracking_ofWalk_of_isPath p.toWalk hpath
  have hlen := length_toWalk p
  have hvertices := vertices_ofWalk p.toWalk
  rw [support_toWalk] at hvertices
  have : ofWalk p.toWalk = hlen.symm ▸ p := by
    apply vertices_injective
    simpa only [vertices_cast] using hvertices
  rw [this] at hnb
  simpa only [nonbacktracking_cast] using hnb

/-- Every reachable vertex has a nonbacktracking based walk of length equal to
its Mathlib distance from the origin. -/
theorem exists_geodesic {x y : V} (hxy : G.Reachable x y) :
    ∃ p : BasedWalk G (G.dist x y) x, p.Nonbacktracking ∧ p.endpoint = y := by
  obtain ⟨p, hp, hlen⟩ := hxy.exists_path_of_dist
  have hnb := nonbacktracking_ofWalk_of_isPath p hp
  have hend := endpoint_ofWalk p
  exact ⟨hlen ▸ ofWalk p, by simpa using hnb, by simpa using hend⟩

end SimpleGraph.BasedWalk
