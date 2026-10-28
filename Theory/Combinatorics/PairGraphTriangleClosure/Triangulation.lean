module

public import Theory.Combinatorics.PairGraphTriangleClosure

/-!
# Triangulating the pair graph

All relations below are in the nonabelian walk congruence: no cycle-space
quotient is used. A diameter-two graph reduces to closed walks of length at
most five by replacing the tail of a walk with a short path. Squares fill by
moving through the connected graph of common neighbors. A chordless pentagon
fills using a common neighbor of one vertex and its opposite edge.

This is the route of Aschbacher, *Sporadic Groups*, §§33–34 (34.5, 34.6,
34.8), applied to the pair graph as in Aschbacher–Smith, §5.2, printed p.658.
-/

@[expose] public section

open SimpleGraph
namespace SimpleGraph.WalkClosure
variable {V : Type*} {Γ : SimpleGraph V} {S : Cycles Γ}

/-- A null closed walk identifies its two parallel sides. -/
theorem rel_of_closed {x y} (p q : Γ.Walk x y)
    (h : Rel S (p.append q.reverse) .nil) : Rel S p q := by
  have hc : Rel S (q.reverse.append q) .nil := by
    simpa using (Rel.cancel (S := S) q.reverse)
  have h₁ := Rel.append (Rel.refl p) hc
  have h₂ := Rel.append h (Rel.refl q)
  simp only [Walk.append_nil] at h₁
  simp only [Walk.nil_append, ← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

/-- Replace two sides of a triangle with its third side. -/
theorem triangle_replace {x y z} (hxy : Γ.Adj x y) (hyz : Γ.Adj y z)
    (hxz : Γ.Adj x z) :
    Rel (triangles Γ) (.cons hxy (.cons hyz .nil)) (.cons hxz .nil) := by
  apply rel_of_closed
  apply Rel.cycle
  rfl

/-- Delete an immediate backtrack at the start of a walk. -/
theorem spur {x y z} (h : Γ.Adj x y) (p : Γ.Walk x z) :
    Rel S (.cons h (.cons h.symm p)) p := by
  simpa using Rel.append (Rel.cancel (S := S) (.cons h .nil)) (Rel.refl p)

/-- Walk equivalence is preserved by prefixing an edge. -/
theorem rel_cons {x y z} (h : Γ.Adj x y) {p q : Γ.Walk y z}
    (hpq : Rel S p q) : Rel S (.cons h p) (.cons h q) :=
  Rel.append (.refl (.cons h .nil)) hpq

/-- A bounded-diameter graph is triangulable once its short closed walks are. -/
theorem triangulable_of_short (d : ℕ)
    (hd : ∀ x y, ∃ p : Γ.Walk x y, p.length ≤ d)
    (hs : ∀ x (p : Γ.Walk x x), p.length ≤ 2 * d + 1 →
      Rel (triangles Γ) p .nil) : Triangulable Γ := by
  have normalize : ∀ {x y} (p : Γ.Walk x y) (q : Γ.Walk x y), q.length ≤ d →
      Rel (triangles Γ) p q := by
    intro x y p
    induction p with
    | nil =>
      intro q hq
      apply Rel.symm
      exact hs _ q (by omega)
    | @cons x z y hxz p ih =>
      intro q hq
      obtain ⟨r, hr⟩ := hd z y
      apply (rel_cons hxz (ih r hr)).trans
      apply rel_of_closed
      apply hs
      simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]
      omega
  intro x p
  exact normalize p .nil (Nat.zero_le _)
end SimpleGraph.WalkClosure

namespace Theory.Combinatorics.PairGraph
open SimpleGraph.WalkClosure
variable {α : Type*} [DecidableEq α]

private theorem neighbor_step {x y u v : Vertex α}
    (hxu : (graph α).Adj x u) (huy : (graph α).Adj u y)
    (hxv : (graph α).Adj x v) (hvy : (graph α).Adj v y)
    (huv : (graph α).Adj u v) :
    Rel (triangles (graph α)) (.cons hxu (.cons huy .nil))
      (.cons hxv (.cons hvy .nil)) := by
  have h₁ := rel_cons hxu (triangle_replace huv hvy huy).symm
  have h₂ := Rel.append (triangle_replace hxu huv hxv) (Rel.refl (.cons hvy .nil))
  exact h₁.trans h₂

/-- The two length-two sides of any square are equivalent modulo triangles. -/
theorem square_paths {x y u v : Vertex α}
    (hxu : (graph α).Adj x u) (huy : (graph α).Adj u y)
    (hxv : (graph α).Adj x v) (hvy : (graph α).Adj v y) :
    Rel (triangles (graph α)) (.cons hxu (.cons huy .nil))
      (.cons hxv (.cons hvy .nil)) := by
  by_cases heq : x = y
  · subst y
    exact (spur hxu .nil).trans (spur hxv .nil).symm
  by_cases hadj : (graph α).Adj x y
  · exact (triangle_replace hxu huy hadj).trans (triangle_replace hxv hvy hadj).symm
  let C := {w | (graph α).Adj x w ∧ (graph α).Adj y w}
  have aux : ∀ {a b : C} (p : ((graph α).induce C).Walk a b),
      Rel (triangles (graph α))
        (.cons a.property.1 (.cons a.property.2.symm .nil))
        (.cons b.property.1 (.cons b.property.2.symm .nil)) := by
    intro a b p
    induction p with
    | nil => exact .refl _
    | @cons a c b hac p ih =>
      exact (neighbor_step a.property.1 a.property.2.symm
        c.property.1 c.property.2.symm hac).trans ih
  let a : C := ⟨u, hxu, huy.symm⟩
  let b : C := ⟨v, hxv, hvy.symm⟩
  obtain ⟨p⟩ := (common_neighbors_connected (disjoint_of_ne_not_adj heq hadj)).preconnected a b
  exact aux p

/-- Every four-edge closed walk fills with triangles. -/
theorem square_fill {x a b c : Vertex α}
    (hxa : (graph α).Adj x a) (hab : (graph α).Adj a b)
    (hbc : (graph α).Adj b c) (hcx : (graph α).Adj c x) :
    Rel (triangles (graph α)) (.cons hxa (.cons hab (.cons hbc (.cons hcx .nil))))
      .nil := by
  have h := Rel.append (square_paths hxa hab hcx.symm hbc.symm)
    (Rel.refl (.cons hbc (.cons hcx .nil)))
  exact h.trans ((rel_cons hcx.symm (spur hbc.symm _)).trans (spur hcx.symm .nil))

/-- Every five-edge closed walk fills with triangles. -/
theorem pentagon_fill {x a b c d : Vertex α}
    (hxa : (graph α).Adj x a) (hab : (graph α).Adj a b)
    (hbc : (graph α).Adj b c) (hcd : (graph α).Adj c d)
    (hdx : (graph α).Adj d x) :
    Rel (triangles (graph α))
      (.cons hxa (.cons hab (.cons hbc (.cons hcd (.cons hdx .nil))))) .nil := by
  by_cases hxb : x = b
  · subst b
    exact (spur hxa _).trans (.cycle _ rfl)
  by_cases hxc : x = c
  · subst c
    have h := Rel.append (Rel.cycle (S := triangles (graph α))
      (.cons hxa (.cons hab (.cons hbc .nil))) rfl) (Rel.refl (.cons hcd (.cons hdx .nil)))
    exact h.trans (spur hcd .nil)
  by_cases hxb' : (graph α).Adj x b
  · exact (Rel.append (triangle_replace hxa hab hxb')
      (Rel.refl (.cons hbc (.cons hcd (.cons hdx .nil))))).trans
        (square_fill hxb' hbc hcd hdx)
  by_cases hxc' : (graph α).Adj x c
  · have h := Rel.append (square_paths hxa hab hxc' hbc.symm)
      (Rel.refl (.cons hbc (.cons hcd (.cons hdx .nil))))
    exact h.trans ((rel_cons hxc' (spur hbc.symm _)).trans (.cycle _ rfl))
  obtain ⟨w, hxw, hbw, hcw⟩ := triple_common_neighbor
    (disjoint_of_ne_not_adj hxb hxb') (disjoint_of_ne_not_adj hxc hxc') hbc
  have h₁ := Rel.append (square_paths hxa hab hxw hbw.symm)
    (Rel.refl (.cons hbc (.cons hcd (.cons hdx .nil))))
  have h₂ := rel_cons hxw (Rel.append (triangle_replace hbw.symm hbc hcw.symm)
    (Rel.refl (.cons hcd (.cons hdx .nil))))
  exact h₁.trans (h₂.trans (square_fill hxw hcw.symm hcd hdx))

/-- Pair graphs are triangulable in the nonabelian closed-walk sense. -/
theorem triangulable : Triangulable (graph α) := by
  apply triangulable_of_short 2
  · intro x y
    rcases distance_le_two x y with rfl | h | ⟨w, hxw, hwy⟩
    · exact ⟨.nil, by simp⟩
    · exact ⟨.cons h .nil, by simp⟩
    · exact ⟨.cons hxw (.cons hwy .nil), by simp⟩
  · intro x p hp
    cases p with
    | nil => exact .refl _
    | cons h₁ p =>
      cases p with
      | nil => exact (h₁.ne rfl).elim
      | cons h₂ p =>
        cases p with
        | nil => exact spur h₁ .nil
        | cons h₃ p =>
          cases p with
          | nil => exact .cycle _ rfl
          | cons h₄ p =>
            cases p with
            | nil => exact square_fill h₁ h₂ h₃ h₄
            | cons h₅ p =>
              cases p with
              | nil => exact pentagon_fill h₁ h₂ h₃ h₄ h₅
              | cons h₆ p =>
                simp only [Walk.length_cons] at hp
                omega
end Theory.Combinatorics.PairGraph
