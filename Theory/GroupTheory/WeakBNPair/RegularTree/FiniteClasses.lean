module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness from apartment shortening

Finite valences give finite balls even in an infinite graph. A path of length
`2 * n` agreeing with a geodesic for its first `n + 1` steps ends strictly
closer to the chosen base vertex: its remaining tail has length at most
`n - 1`. Strong induction then places every equivalence class in a finite
ball. Neither a finite quotient nor a global diameter bound is assumed.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, first paragraph of the proof of (3.6), printed pp.77--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
universe v
variable {V : Type v} (Γ : SimpleGraph V)

/-- Vertices reached by a walk of bounded length. -/
def walkBall (a : V) (n : ℕ) : Set V :=
  {b | ∃ p : Γ.Walk a b, p.length ≤ n}

/-- Finite valences suffice for finite balls; the ambient graph may be infinite. -/
theorem walkBall_finite (hfinite : ∀ a, (Γ.neighborSet a).Finite) (a : V) (n : ℕ) :
    (walkBall Γ a n).Finite := by
  induction n generalizing a with
  | zero =>
    apply (Set.finite_singleton a).subset
    rintro b ⟨p, hp⟩
    have hzero : p.length = 0 := Nat.eq_zero_of_le_zero hp
    exact (SimpleGraph.Walk.eq_of_length_eq_zero hzero).symm
  | succ n ih =>
    apply ((Set.finite_singleton a).union
      ((hfinite a).biUnion fun b _ => ih b)).subset
    rintro b ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a c b hac p =>
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr
        ⟨hac, ⟨p, Nat.le_of_succ_le_succ hp⟩⟩⟩

/-- Continuing an apartment segment past a geodesic prefix of length
`n + 1` gives a strict decrease. Only the tail length is used, so no unproved
metric or geodesicity assertion is hidden in the calculation. -/
theorem closer_of_long_prefix (hconn : Γ.Connected) {a x y : V} {n : ℕ}
    (p : Γ.Walk x y) (hp : p.length = 2 * n)
    (hprefix : Γ.dist a (p.getVert (n + 1)) + (n + 1) = Γ.dist a x) :
    Γ.dist a y < Γ.dist a x := by
  have htail := SimpleGraph.dist_le (p.drop (n + 1))
  rw [SimpleGraph.Walk.drop_length, hp] at htail
  have htri := hconn.dist_triangle (u := a) (v := p.getVert (n + 1)) (w := y)
  omega

/-- Every class has a bounded representative if a related vertex can always
be moved closer outside the bound. This is the distance induction of DGS (3.6). -/
theorem exists_bounded_representative (r : Setoid V) (a : V) (n : ℕ)
    (hshort : ∀ x, n < Γ.dist a x → ∃ y, r x y ∧ Γ.dist a y < Γ.dist a x) :
    ∀ x, ∃ y, r x y ∧ Γ.dist a y ≤ n := by
  suffices ∀ d x, Γ.dist a x = d → ∃ y, r x y ∧ Γ.dist a y ≤ n by
    intro x
    exact this _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro x hx
    by_cases hle : Γ.dist a x ≤ n
    · exact ⟨x, r.refl x, hle⟩
    · obtain ⟨y, hxy, hlt⟩ := hshort x (Nat.lt_of_not_ge hle)
      obtain ⟨z, hyz, hz⟩ := ih _ (hx ▸ hlt) y rfl
      exact ⟨z, r.trans hxy hyz, hz⟩

/-- A locally finite connected graph with this shortening operation has
finitely many equivalence classes. No finite quotient is assumed. -/
theorem finite_classes_of_shortening (hconn : Γ.Connected)
    (hfinite : ∀ a, (Γ.neighborSet a).Finite) (r : Setoid V) (a : V) (n : ℕ)
    (hshort : ∀ x, n < Γ.dist a x → ∃ y, r x y ∧ Γ.dist a y < Γ.dist a x) :
    Finite (Quotient r) := by
  have : Finite (walkBall Γ a n) := (walkBall_finite Γ hfinite a n).to_subtype
  apply Finite.of_surjective (fun x : walkBall Γ a n => Quotient.mk r x.val)
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨y, hxy, hy⟩ := exists_bounded_representative Γ r a n hshort x
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a y
    exact ⟨⟨y, p, hp ▸ hy⟩, Quotient.sound (r.symm hxy)⟩

end Theory.GroupTheory.WeakBNPair.RegularTree
