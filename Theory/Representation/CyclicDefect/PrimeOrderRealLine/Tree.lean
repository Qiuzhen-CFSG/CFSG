module

public import Theory.Representation.CyclicDefect.RealLine
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The module-valued tree before choosing a path ordering

For exceptional multiplicity one, vertices are the actual ordinary block
rows and edges carry actual simple modules. The unordered pairs of endpoints
are distinct, and their graph is a tree. The regular decomposition and
projective-character identities retain the chosen root correspondence.

This is a shared output interface for Feit VII.2.11--15 and VII.6.8, not an
existence assertion. The real-valency theorem VII.2.24 is deliberately not a
field. Evaluating the decomposition at one proves that a degree-one vertex
has exactly one incident edge; thus the principal character is an endpoint
once a tree has been constructed.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine

/-- The graph determined by a family of unordered endpoint pairs. -/
@[expose] def endpointGraph {V : Type*} {n : ℕ} (left right : Fin n → V) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range fun e => s(left e, right e))

/-- The multiplicity-one cyclic-defect output, before real valency and ordering.
There is no existence instance. In particular projectivity is genuine
projectivity over the group algebra, not a numerical character condition. -/
structure Tree {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] (χ : I → ConjClassFunction G) (block : Finset I)
    (p : ℕ) {m : ℕ} (n : ℕ) (L : CyclicRootLift K m) where
  left : Fin n → {i // i ∈ block}
  right : Fin n → {i // i ∈ block}
  endpoints_ne : ∀ e, left e ≠ right e
  edges_injective : Function.Injective (fun e => s(left e, right e))
  isTree : (endpointGraph left right).IsTree
  degree : Fin n → ℕ
  rep : ∀ e, Representation K G (Fin (degree e) → K)
  irreducible : ∀ e, Representation.IsIrreducible (rep e)
  inequivalent : Pairwise fun e f => IsEmpty ((rep e).Equiv (rep f))
  decomposition : ∀ g, ¬ p ∣ orderOf g → ∀ v : {i // i ∈ block},
    χ v.val (ConjClasses.mk g) =
      ∑ e, if v = left e ∨ v = right e then L.value (rep e) g else 0
  projective : ∀ e, ProjectiveCharacterLift p L
    (fun g => χ (left e).val (ConjClasses.mk g) + χ (right e).val (ConjClasses.mk g))

namespace Tree

variable {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] {χ : I → ConjClassFunction G} {block : Finset I}
    {p m n : ℕ} {L : CyclicRootLift K m} (t : Tree χ block p n L)

/-- Incident edges, with the literal endpoints used in the decomposition. -/
@[expose] def incident (v : {i // i ∈ block}) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => v = t.left e ∨ v = t.right e

@[simp] theorem mem_incident (v : {i // i ∈ block}) (e : Fin n) :
    e ∈ t.incident v ↔ v = t.left e ∨ v = t.right e := by
  classical
  simp [incident]

/-- Counting the actual incident modules is exactly graph-theoretic valency.
Distinct unordered endpoint pairs exclude parallel edges. -/
theorem graph_degree_eq_incident_card (v : {i // i ∈ block}) :
    (endpointGraph t.left t.right).degree v = (t.incident v).card := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  symm
  apply Finset.card_bij (fun e _ => s(t.left e, t.right e))
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
    refine ⟨?_, (t.mem_incident v e).mp he⟩
    exact ⟨⟨e, rfl⟩, t.endpoints_ne e⟩
  · intro e he f hf hef
    exact t.edges_injective hef
  · intro edge hedge
    have hi := (SimpleGraph.mem_incidenceFinset _ _ _).mp hedge
    have he := hi.1
    change edge ∈ (SimpleGraph.fromEdgeSet _).edgeSet at he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨e, rfl⟩ := he.1
    exact ⟨e, (t.mem_incident v e).mpr (Sym2.mem_iff.mp hi.2), rfl⟩

/-- Simplicity excludes zero-dimensional edge modules. -/
theorem degree_pos (e : Fin n) : 0 < t.degree e := by
  let : Representation.IsIrreducible (t.rep e) := t.irreducible e
  let : Nontrivial (t.rep e).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra K G) (t.rep e).asModule
  let : Nontrivial (Fin (t.degree e) → K) :=
    Function.Injective.nontrivial (t.rep e).asModuleEquiv.injective
  simpa using (Module.finrank_pos (R := K) (M := Fin (t.degree e) → K))

/-- Degree is the sum of the actual natural dimensions at the incident edges. -/
theorem sum_degrees (hp : p ≠ 1) (v : {i // i ∈ block}) {d : ℕ}
    (hd : χ v.val (ConjClasses.mk 1) = (d : ℂ)) :
    ∑ e ∈ t.incident v, t.degree e = d := by
  classical
  have h := t.decomposition 1 (by simpa using hp) v
  rw [hd] at h
  simp only [CyclicRootLift.value_one, Module.finrank_pi, Fintype.card_fin] at h
  have hc : ((∑ e ∈ t.incident v, t.degree e : ℕ) : ℂ) =
      ∑ e, if v = t.left e ∨ v = t.right e then (t.degree e : ℂ) else 0 := by
    simp [incident, Finset.sum_filter]
  rw [← hc] at h
  exact_mod_cast h.symm

/-- A degree-one ordinary row is an endpoint. This uses irreducibility of the
edge modules and the lifted character identity, not graph realness. -/
theorem incident_card_eq_one (hp : p ≠ 1) (v : {i // i ∈ block})
    (hd : χ v.val (ConjClasses.mk 1) = 1) :
    (t.incident v).card = 1 := by
  have hs : ∑ e ∈ t.incident v, t.degree e = 1 := t.sum_degrees hp v (by simpa using hd)
  have hle : (t.incident v).card ≤ ∑ e ∈ t.incident v, t.degree e := by
    calc
      (t.incident v).card = ∑ _e ∈ t.incident v, 1 := by simp
      _ ≤ ∑ e ∈ t.incident v, t.degree e :=
        Finset.sum_le_sum fun e _ => t.degree_pos e
  have hn : (t.incident v).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hs
    simp at hs
  have hpos := Finset.card_pos.mpr hn
  omega

end Tree
end Representation.CyclicDefect.PrimeOrderRealLine
