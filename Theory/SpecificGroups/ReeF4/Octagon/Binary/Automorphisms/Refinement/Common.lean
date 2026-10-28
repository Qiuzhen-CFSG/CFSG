module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
public import Theory.Combinatorics.SimpleGraph.ColorRefinement

/-!
# Shared arithmetic for the binary-octagon refinement certificate

The initial colors distinguish the ten vertices of a fixed nine-edge path.
Each following stage uses the symmetric neighbor signature from the general
soundness theorem, followed by a deterministic finite-table lookup. The
lookup need not be injective: the checked final color separation is what
proves rigidity. Interval assembly keeps kernel checks in bounded blocks.

Source: the building-automorphism step in Aschbacher--Smith J.5.6, printed p.447.
-/

@[expose] public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteGraph.Refinement

/-- Initial path labels, with one common color off the path. -/
def color0 (i : ℕ) : ℕ :=
  if i=0 then 1 else if i=1755 then 2 else if i=1 then 3 else
  if i=1757 then 4 else if i=4 then 5 else if i=1766 then 6 else
  if i=19 then 7 else if i=1813 then 8 else if i=100 then 9 else
  if i=1867 then 10 else 0

/-- Raw-coordinate version of the invariant neighbor signature. -/
def rawSignature (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  c i+1 + 8192 * ((adjacency i).map (fun j =>
    SimpleGraph.ColorRefinement.moment (c j))).sum

/-- A deterministic bounded binary lookup; correctness is checked pointwise. -/
def locate (key : ℕ → ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi => if hi ≤ lo+1 then lo else
      let mid := (lo+hi)/2
      if k < key mid then locate key k fuel lo mid else locate key k fuel mid hi

/-- Interpret one checked finite block as an interval statement. -/
theorem of_block (P : ℕ → Prop) (lo len : ℕ)
    (h : ∀ j : Fin len, P (j.val+lo)) :
    ∀ i, lo ≤ i → i < lo+len → P i := by
  intro i hlo hi
  have hh := h ⟨i-lo, by omega⟩
  have he : i-lo+lo=i := by omega
  simpa only [he] using hh

/-- Join adjacent verified intervals without a large finite case tree. -/
theorem join {P : ℕ → Prop} {lo mid hi : ℕ}
    (left : ∀ i, lo ≤ i → i < mid → P i)
    (right : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact left i hlo hm
  · exact right i (Nat.le_of_not_gt hm) hhi

end ReeF4.Octagon.Binary.Automorphisms.FiniteGraph.Refinement
