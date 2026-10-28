module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lower bounds from finite orbit trees

A rooted tree whose edges are actions of specified group elements supplies
explicit reachability witnesses. Distinct reached points give disjoint cosets
of the point stabilizer, and hence a lower bound for the group cardinality.
Neither closure of the reached set nor generation by the specified elements
is required: this is a lower-bound certificate only.

These elementary orbit–stabilizer arguments are extracted from the private
helpers in `Held/Automorphisms/Normalizer/LowerBound.lean` for reuse by the
literal Held 2A centralizer certificate.
-/

public section
namespace MulAction

theorem card_lower_bound_of_reachable {G X : Type*} [Group G] [MulAction G X]
    [Finite G] {m : ℕ} (b : X) (point : Fin m → X)
    (hi : Function.Injective point)
    (hr : ∀ i, ∃ g : G, g • b = point i) :
    m * Nat.card (MulAction.stabilizer G b) ≤ Nat.card G := by
  classical
  choose rep hrep using hr
  have hinj : Function.Injective (fun z : Fin m × MulAction.stabilizer G b =>
      rep z.1 * z.2.val) := by
    rintro ⟨i, g⟩ ⟨j, h⟩ heq
    have hij : i = j := hi (by
      have he := congrArg (fun k : G => k • b) heq
      simpa only [mul_smul, MulAction.mem_stabilizer_iff.mp g.property,
        MulAction.mem_stabilizer_iff.mp h.property, hrep] using he)
    subst j
    have hgh : g = h := Subtype.ext (mul_left_cancel heq)
    subst h
    rfl
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective _ hinj

theorem exists_smul_eq_of_orbit_tree {G X : Type*} [Group G] [MulAction G X]
    {m r : ℕ} [NeZero m] (gen : Fin r → G) (b : X) (point : Fin m → X)
    (parent : Fin m → Fin m) (step : Fin m → Fin r) (depth : Fin m → ℕ)
    (hbase : point 0 = b)
    (hstep : ∀ i, i = 0 ∨ (depth (parent i) < depth i ∧
      gen (step i) • point (parent i) = point i)) :
    ∀ i, ∃ g : G, g • b = point i := by
  suffices h : ∀ n : ℕ, ∀ i, depth i = n → ∃ g : G, g • b = point i from
    fun i => h (depth i) i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    rcases hstep i with rfl | ⟨hd, hs⟩
    · exact ⟨1, by simpa using hbase.symm⟩
    · obtain ⟨g, hg⟩ := ih (depth (parent i)) (by omega) (parent i) rfl
      exact ⟨gen (step i) * g, by rw [mul_smul, hg, hs]⟩


end MulAction
