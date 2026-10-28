module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Mathlib.Data.Set.Card

/-!
# Nonbacktracking walks in a set with two neighbors at each vertex

The first oriented edge determines a nonbacktracking walk lying in such a
set. After the first step the preceding vertex excludes one of the two
neighbors, so induction determines every remaining vertex. These literal
vertex-list equalities are used for the normalizer apartments of the Ree
octagon in Aschbacher–Smith F.4.8.
-/

public section
namespace SimpleGraph.BasedWalk
variable {V : Type*} {G : SimpleGraph V}

private theorem neighbor_choice (A : Set V)
    (hA : ∀ x ∈ A, {y | y ∈ A ∧ G.Adj x y}.ncard = 2)
    {x a b c : V} (hx : x ∈ A) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c) (hab : a ≠ b) :
    c = a ∨ c = b := by
  obtain ⟨u, v, _, huv⟩ := Set.ncard_eq_two.mp (hA x hx)
  have ha' : a ∈ ({y | y ∈ A ∧ G.Adj x y} : Set V) := ⟨ha, hxa⟩
  have hb' : b ∈ ({y | y ∈ A ∧ G.Adj x y} : Set V) := ⟨hb, hxb⟩
  have hc' : c ∈ ({y | y ∈ A ∧ G.Adj x y} : Set V) := ⟨hc, hxc⟩
  simp only [huv, Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb' hc'
  aesop

/-- A nonbacktracking walk in a two-neighbor set is determined by its first edge. -/
theorem vertices_eq_of_first_of_two_neighbors (A : Set V)
    (hA : ∀ x ∈ A, {y | y ∈ A ∧ G.Adj x y}.ncard = 2)
    {n : ℕ} {x y : V} (p : BasedWalk G (n + 1) x) (q : BasedWalk G (n + 1) y)
    (hxy : x = y) (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (hpA : ∀ v ∈ p.vertices, v ∈ A) (hqA : ∀ v ∈ q.vertices, v ∈ A)
    (hfirst : (p.1 : V) = (q.1 : V)) : p.vertices = q.vertices := by
  subst y
  induction n generalizing x with
  | zero =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    have he : a = b := Subtype.ext hfirst
    subst b
    rfl
  | succ n ih =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    have he : a = b := Subtype.ext hfirst
    subst b
    have hxA : x ∈ A := hpA x (by simp only [vertices, List.mem_cons, true_or])
    have haA : (a : V) ∈ A := hpA a (by
      change (a : V) ∈ x :: a.val :: _
      simp only [List.mem_cons, true_or, or_true])
    have hpA' : ∀ v ∈ p.vertices, v ∈ A := fun v hv => hpA v (List.mem_cons_of_mem x hv)
    have hqA' : ∀ v ∈ q.vertices, v ∈ A := fun v hv => hqA v (List.mem_cons_of_mem x hv)
    have hp1A : (p.1 : V) ∈ A := hpA' p.1 (by
      have hh := p.2.toWalk.start_mem_support
      rw [support_toWalk] at hh
      exact List.mem_cons_of_mem _ hh)
    have hq1A : (q.1 : V) ∈ A := hqA' q.1 (by
      have hh := q.2.toWalk.start_mem_support
      rw [support_toWalk] at hh
      exact List.mem_cons_of_mem _ hh)
    have hnext : (p.1 : V) = (q.1 : V) := by
      have hc := neighbor_choice A hA haA hxA hp1A hq1A a.property.symm
        p.1.property q.1.property hp.1.symm
      exact (hc.resolve_left hq.1).symm
    exact congrArg (List.cons x) (ih p hp.2 hpA' q hq.2 hqA' hnext)

/-- Removing the final edge leaves the original penultimate vertex. -/
theorem endpoint_take_penultimate {n : ℕ} {x : V} (p : BasedWalk G (n + 1) x) :
    (p.take n (Nat.le_succ n)).endpoint = p.penultimate := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2

/-- A positive-length vertex list is its prefix followed by its final vertex. -/
theorem vertices_eq_prefix_append_endpoint {n : ℕ} {x : V} (p : BasedWalk G (n + 1) x) :
    p.vertices = (p.take n (Nat.le_succ n)).vertices ++ [p.endpoint] := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons x) (ih p.2)

end SimpleGraph.BasedWalk
