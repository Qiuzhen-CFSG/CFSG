module

public import Theory.GroupAction.CubicTree.ArcRegularity

/-!
# Reversing regular arcs

The reverse is constructed inside the existing `BasedWalk` representation by
reversing the tail and appending the original starting vertex. It preserves
nonbacktracking and exchanges the two endpoint extension sets. These are the
reversal steps in Goldschmidt (2.12), printed pp.383--384.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

/-- Recursive reversal together with its endpoint equation. -/
def reverseData : {n : ℕ} → {x : V} → (p : BasedWalk Γ n x) →
    {q : BasedWalk Γ n p.endpoint // q.endpoint = x}
  | 0, _, _ => ⟨PUnit.unit, rfl⟩
  | _ + 1, _, p =>
    let q := reverseData p.2
    ⟨q.val.snoc (by rw [q.property]; exact p.1.property.symm),
      BasedWalk.endpoint_snoc _ _⟩

/-- The literal opposite ordered arc. -/
abbrev reverse {n : ℕ} {x : V} (p : BasedWalk Γ n x) : BasedWalk Γ n p.endpoint :=
  (reverseData p).val

@[simp] theorem endpoint_reverse {n : ℕ} {x : V} (p : BasedWalk Γ n x) :
    (reverse p).endpoint = x := (reverseData p).property

@[simp] theorem vertices_reverse {n : ℕ} {x : V} (p : BasedWalk Γ n x) :
    (reverse p).vertices = p.vertices.reverse := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change ((reverse p.2).snoc _).vertices = (x :: p.2.vertices).reverse
    rw [BasedWalk.vertices_snoc, ih, List.reverse_cons]

@[simp] theorem penultimate_reverse {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x) :
    (reverse p).penultimate = p.1 := by
  change ((reverse p.2).snoc _).penultimate = _
  rw [BasedWalk.penultimate_snoc, endpoint_reverse]

theorem nonbacktracking_reverse {n : ℕ} {x : V} (p : BasedWalk Γ n x)
    (hp : p.Nonbacktracking) : (reverse p).Nonbacktracking := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    cases n with
    | zero => trivial
    | succ n =>
      change ((reverse p.2).snoc _).Nonbacktracking
      rw [BasedWalk.nonbacktracking_snoc_iff]
      exact ⟨ih p.2 hp.2, by simpa only [penultimate_reverse] using hp.1.symm⟩

theorem forward_reverse_iff_backward {n : ℕ} {x z : V} (p : BasedWalk Γ n x) :
    Forward (reverse p) z ↔ Backward p z := by
  cases n with
  | zero => rfl
  | succ n => simp only [Forward, Backward, endpoint_reverse, penultimate_reverse]

/-- Reversal exchanges right regularity and left regularity. -/
theorem rightRegular_reverse_iff {n : ℕ} {x : V} (p : BasedWalk Γ n x) :
    RightRegular (A := A) (reverse p) ↔ LeftRegular (A := A) p := by
  simp only [RightRegular, LeftRegular, forward_reverse_iff_backward,
    vertices_reverse, List.mem_reverse]

theorem first_reverse {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x) :
    ((reverse p).1 : V) = p.penultimate := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2

theorem backward_reverse_iff_forward {n : ℕ} {x z : V} (p : BasedWalk Γ n x) :
    Backward (reverse p) z ↔ Forward p z := by
  cases n with
  | zero => rfl
  | succ n => simp only [Backward, Forward, first_reverse]

theorem leftRegular_reverse_iff {n : ℕ} {x : V} (p : BasedWalk Γ n x) :
    LeftRegular (A := A) (reverse p) ↔ RightRegular (A := A) p := by
  simp only [LeftRegular, RightRegular, backward_reverse_iff_forward,
    vertices_reverse, List.mem_reverse]

/-- Using right regularity at every starting vertex suffices to recover both
endpoint regularity conditions at shorter lengths. -/
theorem regular_of_all_rightRegular {n : ℕ}
    (hall : ∀ (x : V) (p : BasedWalk Γ n x), p.Nonbacktracking → RightRegular (A := A) p)
    {x : V} (p : BasedWalk Γ n x) (hp : p.Nonbacktracking) : Regular (A := A) p :=
  ⟨(rightRegular_reverse_iff p).1 (hall _ _ (nonbacktracking_reverse p hp)), hall x p hp⟩

end Theory.GroupAction.CubicTree
