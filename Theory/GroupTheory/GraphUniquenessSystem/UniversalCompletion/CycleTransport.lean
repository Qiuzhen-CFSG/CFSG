module

public import Theory.Combinatorics.PairGraphTriangleClosure.WalkClosure
public import Mathlib.Logic.Equiv.Basic

/-!
# Transport invariant under normal cycle closure

Reversible transport along graph edges extends to walks. If the generating
cycles have trivial transport, the same holds for their normal closure, including
conjugates and reversed cycles. A cycle base therefore makes transport depend
only on endpoints. This is the path-lifting mechanism needed in the universal
completion argument for a graph uniqueness system.

Source: Aschbacher, *Sporadic Groups* (1994), §§33 and 35, especially 35.14–35.16.
-/

@[expose] public section

namespace SimpleGraph.WalkClosure

universe u w
variable {V : Type u} {Γ : SimpleGraph V}

/-- Reversible edge transport in an arbitrary family of fibers. -/
structure Transport (Γ : SimpleGraph V) (F : V → Type w) where
  edge : ∀ {x y}, Γ.Adj x y → F x ≃ F y
  reverse_edge : ∀ {x y} (h : Γ.Adj x y), edge h.symm = (edge h).symm

namespace Transport
variable {F : V → Type w} (T : Transport Γ F)

/-- Compose the edge equivalences along a walk. -/
def along : {x y : V} → Γ.Walk x y → F x ≃ F y
  | _, _, .nil => Equiv.refl _
  | _, _, .cons h p => (T.edge h).trans (along p)

@[simp] theorem along_nil (x : V) : T.along (.nil : Γ.Walk x x) = Equiv.refl _ := rfl

@[simp] theorem along_cons {x y z : V} (h : Γ.Adj x y) (p : Γ.Walk y z) :
    T.along (.cons h p) = (T.edge h).trans (T.along p) := rfl

/-- Concatenation corresponds to composition of transport. -/
theorem along_append {x y z : V} (p : Γ.Walk x y) (q : Γ.Walk y z) :
    T.along (p.append q) = (T.along p).trans (T.along q) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.cons_append, along_cons, ih]
    rfl

/-- Reversing a walk inverts its transport. -/
theorem along_reverse {x y : V} (p : Γ.Walk x y) :
    T.along p.reverse = (T.along p).symm := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Walk.reverse_cons, T.along_append, ih]
    change (T.along p).symm.trans ((T.edge h.symm).trans (Equiv.refl _)) = _
    rw [T.reverse_edge]
    rfl

/-- Killing the generators suffices to preserve every normal cycle relation. -/
theorem along_rel {S : Cycles Γ}
    (hS : ∀ x (p : Γ.Walk x x), p ∈ S x → T.along p = Equiv.refl _)
    {x y : V} {p q : Γ.Walk x y} (h : Rel S p q) : T.along p = T.along q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | append _ _ ih₁ ih₂ => rw [T.along_append, T.along_append, ih₁, ih₂]
  | reverse _ ih => rw [T.along_reverse, T.along_reverse, ih]
  | cancel p =>
    rw [T.along_append, T.along_reverse]
    ext a
    exact (T.along p).symm_apply_apply a
  | cycle p hp => exact hS _ p hp

/-- All cycles in a cycle base's normal closure have trivial transport. -/
theorem along_loop {S : Cycles Γ} (hbase : IsCycleBase S)
    (hS : ∀ x (p : Γ.Walk x x), p ∈ S x → T.along p = Equiv.refl _)
    {x : V} (p : Γ.Walk x x) : T.along p = Equiv.refl _ :=
  T.along_rel hS (hbase x p)

/-- Over a cycle base, parallel walks give identical transport. -/
theorem along_eq {S : Cycles Γ} (hbase : IsCycleBase S)
    (hS : ∀ x (p : Γ.Walk x x), p ∈ S x → T.along p = Equiv.refl _)
    {x y : V} (p q : Γ.Walk x y) : T.along p = T.along q := by
  have h := T.along_loop hbase hS (p.append q.reverse)
  rw [T.along_append, T.along_reverse] at h
  ext a
  apply (T.along q).symm.injective
  exact (congrArg (fun e : F x ≃ F x => e a) h).trans
    ((T.along q).symm_apply_apply a).symm

end Transport
end SimpleGraph.WalkClosure
