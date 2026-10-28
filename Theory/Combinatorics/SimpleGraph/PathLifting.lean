module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Lifting based walks through graph coverings

A graph homomorphism that is bijective on each neighbor set induces a bijection
on walks of any prescribed length from a chosen vertex. Local injectivity also
preserves and reflects the absence of backtracking. Consequently the same lifting
bijection restricts to nonbacktracking walks, at fixed or arbitrary length.

The construction recursively chooses the first edge, then lifts the remaining
walk. `BasedWalk` is a length-indexed presentation of ordinary graph walks;
`toWalk`, `ofWalk`, and their support lemmas connect it to Mathlib's presentation.
The vertex-list map is injective, so subsequent equivariance arguments can be
checked vertex by vertex.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Definition F.3.2 and the graph-theoretic assertion of
Lemma F.3.3(1), printed pp. 270–271. The ambient amalgam is not needed here.
-/

@[expose] public section

namespace SimpleGraph
universe u v
variable {V : Type u} {W : Type v}

/-- Walks with a fixed origin and length, represented recursively by their first edge. -/
@[reducible] def BasedWalk (G : SimpleGraph V) : ℕ → V → Type u
  | 0, _ => PUnit
  | n + 1, x => Σ y : G.neighborSet x, BasedWalk G n y

namespace BasedWalk
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Apply a graph homomorphism to every vertex of a based walk. -/
def map (f : G →g H) : {n : ℕ} → {x : V} → BasedWalk G n x → BasedWalk H n (f x)
  | 0, _, _ => PUnit.unit
  | _ + 1, _, p => ⟨f.mapNeighborSet _ p.1, map f p.2⟩

/-- Unique lifting of fixed-length based walks along a local bijection. -/
noncomputable def coveringEquiv (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x)) :
    (n : ℕ) → (x : V) → BasedWalk G n x ≃ BasedWalk H n (f x)
  | 0, _ => Equiv.punitEquivPUnit
  | n + 1, x => Equiv.sigmaCongr (Equiv.ofBijective _ (hf x))
      (fun y => coveringEquiv f hf n y)

/-- The lifting equivalence has the ordinary vertex map as its forward map. -/
theorem coveringEquiv_apply (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x))
    {n : ℕ} {x : V} (p : BasedWalk G n x) : coveringEquiv f hf n x p = map f p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨y, p⟩
    exact congrArg (fun q => Sigma.mk (f.mapNeighborSet x y) q) (ih p)

/-- Consecutive edges never immediately return to the preceding vertex. -/
def Nonbacktracking : {n : ℕ} → {x : V} → BasedWalk G n x → Prop
  | 0, _, _ => True
  | 1, _, _ => True
  | _ + 2, x, p => (p.2.1 : V) ≠ x ∧ Nonbacktracking p.2

/-- Local injectivity preserves and reflects the absence of backtracking. -/
theorem nonbacktracking_map_iff (f : G →g H)
    (hf : ∀ x, Function.Injective (f.mapNeighborSet x))
    {n : ℕ} {x : V} (p : BasedWalk G n x) :
    Nonbacktracking (map f p) ↔ Nonbacktracking p := by
  induction n using Nat.twoStepInduction generalizing x with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
    change (f (p.2.1 : V) ≠ f x ∧ Nonbacktracking (map f p.2)) ↔
      ((p.2.1 : V) ≠ x ∧ Nonbacktracking p.2)
    rw [ih]
    have heq : f (p.2.1 : V) = f x ↔ (p.2.1 : V) = x := by
      constructor
      · intro h
        have h' := hf p.1 (a₁ := p.2.1) (a₂ := ⟨x, p.1.2.symm⟩) (Subtype.ext h)
        exact congrArg Subtype.val h'
      · exact congrArg f
    exact and_congr (not_congr heq) Iff.rfl

/-- A local bijection is bijective on walks from a chosen origin. -/
theorem map_bijective (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x)) (n : ℕ) (x : V) :
    Function.Bijective (map f : BasedWalk G n x → BasedWalk H n (f x)) := by
  have h : (map f : BasedWalk G n x → BasedWalk H n (f x)) =
      coveringEquiv f hf n x := by
    funext p
    exact (coveringEquiv_apply f hf p).symm
  rw [h]
  exact (coveringEquiv f hf n x).bijective

/-- Unique lifting restricted to nonbacktracking walks of a prescribed length. -/
noncomputable def nonbacktrackingEquiv (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x)) (n : ℕ) (x : V) :
    {p : BasedWalk G n x // p.Nonbacktracking} ≃
      {p : BasedWalk H n (f x) // p.Nonbacktracking} :=
  (coveringEquiv f hf n x).subtypeEquiv fun p => by
    rw [coveringEquiv_apply]
    exact (nonbacktracking_map_iff f (fun x => (hf x).1) p).symm

/-- Unique lifting of walks of arbitrary finite length. -/
noncomputable def allLengthsEquiv (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x)) (x : V) :
    (Σ n, BasedWalk G n x) ≃ (Σ n, BasedWalk H n (f x)) :=
  Equiv.sigmaCongrRight fun n => coveringEquiv f hf n x

/-- Unique lifting of nonbacktracking walks of arbitrary finite length. -/
noncomputable def allNonbacktrackingEquiv (f : G →g H)
    (hf : ∀ x, Function.Bijective (f.mapNeighborSet x)) (x : V) :
    (Σ n, {p : BasedWalk G n x // p.Nonbacktracking}) ≃
      (Σ n, {p : BasedWalk H n (f x) // p.Nonbacktracking}) :=
  Equiv.sigmaCongrRight fun n => nonbacktrackingEquiv f hf n x

/-- The last vertex of a based walk. -/
def endpoint : {n : ℕ} → {x : V} → BasedWalk G n x → V
  | 0, x, _ => x
  | _ + 1, _, p => endpoint p.2

/-- View a based walk as a Mathlib walk ending at its endpoint. -/
def toWalk : {n : ℕ} → {x : V} → (p : BasedWalk G n x) → G.Walk x p.endpoint
  | 0, _, _ => .nil
  | _ + 1, _, p => .cons p.1.2 (toWalk p.2)

/-- Conversion to a Mathlib walk preserves the length. -/
theorem length_toWalk {n : ℕ} {x : V} (p : BasedWalk G n x) :
    p.toWalk.length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih p.2)

/-- The ordered list of vertices, including the origin and endpoint. -/
def vertices : {n : ℕ} → {x : V} → BasedWalk G n x → List V
  | 0, x, _ => [x]
  | _ + 1, x, p => x :: vertices p.2

/-- Mapping a based walk applies the homomorphism to its vertex list. -/
theorem vertices_map (f : G →g H) {n : ℕ} {x : V} (p : BasedWalk G n x) :
    (map f p).vertices = p.vertices.map f := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons (f x)) (ih p.2)

/-- The Mathlib support list is the based walk vertex list. -/
theorem support_toWalk {n : ℕ} {x : V} (p : BasedWalk G n x) :
    p.toWalk.support = p.vertices := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons x) (ih p.2)

/-- Every Mathlib walk has a length-indexed based walk presentation. -/
def ofWalk {x y : V} (p : G.Walk x y) : BasedWalk G p.length x :=
  match p with
  | .nil => PUnit.unit
  | .cons h p => ⟨⟨_, h⟩, ofWalk p⟩

/-- Conversion from a Mathlib walk preserves its endpoint. -/
theorem endpoint_ofWalk {x y : V} (p : G.Walk x y) : (ofWalk p).endpoint = y := by
  induction p with
  | nil => rfl
  | cons h p ih => exact ih

/-- Conversion from a Mathlib walk preserves its ordered vertices. -/
theorem vertices_ofWalk {x y : V} (p : G.Walk x y) :
    (ofWalk p).vertices = p.support := by
  induction p with
  | nil => rfl
  | @cons x y z h p ih => exact congrArg (List.cons x) ih

/-- The first vertex is the chosen origin. -/
theorem head_vertices {n : ℕ} {x : V} (p : BasedWalk G n x) :
    p.vertices.head? = some x := by
  cases n <;> rfl

/-- A based walk is determined by its ordered vertices. -/
theorem vertices_injective (n : ℕ) (x : V) :
    Function.Injective (vertices : BasedWalk G n x → List V) := by
  induction n generalizing x with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    rintro ⟨⟨y, hxy⟩, p⟩ ⟨⟨z, hxz⟩, q⟩ h
    have ht : p.vertices = q.vertices := (List.cons.inj h).2
    have hyz : y = z := by
      have := congrArg List.head? ht
      rw [head_vertices, head_vertices] at this
      exact Option.some.inj this
    subst z
    have hpq := ih y ht
    subst q
    rfl

end BasedWalk
end SimpleGraph
