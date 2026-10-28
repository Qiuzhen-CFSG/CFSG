module

public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry

/-!
# The cubic orbit span in the binary five-point core

The conjugates of e₁₂₃₄ under (3 4 5) span the hyperplane on which the
first two coordinates agree. Its intersection with the alternating orbit
of e₁₂₃₄ consists of these three vectors, whose sum is e₁₂.
The stabilizer of e₁₂ preserves this hyperplane: it preserves its first
two coordinates as an unordered pair.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, §13.6,
printed pp.926 and 928.
-/

@[expose] public section
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry Subgroup
namespace BinaryPermutation.FiveCentralizerGeometry.SpanGeometry
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _

def plane : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 0 = x.toAdd.val 1}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by
    change x.toAdd.val 0 + y.toAdd.val 0 = x.toAdd.val 1 + y.toAdd.val 1
    rw [hx, hy]
  inv_mem' {x} hx := by
    change -x.toAdd.val 0 = -x.toAdd.val 1
    rw [hx]

local instance : DecidablePred (· ∈ plane) := fun x =>
  inferInstanceAs (Decidable (x.toAdd.val 0 = x.toAdd.val 1))
local instance : Fintype plane := Subtype.fintype _

/-- The cubic orbit spans eight actual binary vectors. -/
theorem plane_card : Nat.card plane = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def point (i : Fin 3) : Space := ![z, act cubic z, act (cubic ^ 2) z] i

theorem point_injective : Function.Injective point := by decide +kernel

theorem points_mem (i : Fin 3) : Multiplicative.ofAdd (point i) ∈ plane := by
  change (point i).val 0 = (point i).val 1
  fin_cases i <;> decide

theorem points_sum : point 0 + point 1 + point 2 = v := orbit_sum

private theorem pair_preserved (g : alternatingGroup (Fin 5)) (hg : act g v = v) :
    (g.val.symm 0 = 0 ∧ g.val.symm 1 = 1) ∨
    (g.val.symm 0 = 1 ∧ g.val.symm 1 = 0) := by
  have hv : ∀ i : Fin 5, v.val i = 1 → i = 0 ∨ i = 1 := by decide
  have h0 := hv (g.val.symm 0) (congrArg (fun x : Space => x.val 0) hg)
  have h1 := hv (g.val.symm 1) (congrArg (fun x : Space => x.val 1) hg)
  have hn : g.val.symm 0 ≠ g.val.symm 1 := g.val.symm.injective.ne (by decide)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact (hn (h0.trans h1.symm)).elim
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact (hn (h0.trans h1.symm)).elim

theorem plane_invariant (g : alternatingGroup (Fin 5)) (hg : act g v = v)
    (x : Multiplicative Space) (hx : x ∈ plane) :
    Multiplicative.ofAdd (act g x.toAdd) ∈ plane := by
  change x.toAdd.val 0 = x.toAdd.val 1 at hx
  change x.toAdd.val (g.val.symm 0) = x.toAdd.val (g.val.symm 1)
  rcases pair_preserved g hg with h | h
  · simpa only [h.1, h.2] using hx
  · simpa only [h.1, h.2] using hx.symm

theorem plane_cases (x : Space) (hx : Multiplicative.ofAdd x ∈ plane) :
    x = 0 ∨ x = point 0 ∨ x = point 1 ∨ x = point 2 ∨
    x = point 0 + point 1 ∨ x = point 0 + point 2 ∨
    x = point 1 + point 2 ∨ x = v := by
  have h : ∀ x : Space, x.val 0 = x.val 1 →
      x = 0 ∨ x = point 0 ∨ x = point 1 ∨ x = point 2 ∨
      x = point 0 + point 1 ∨ x = point 0 + point 2 ∨
      x = point 1 + point 2 ∨ x = v := by decide +kernel
  exact h x hx

private theorem orbit_word (g : alternatingGroup (Fin 5)) (i : Fin 5) :
    (act g z).val i = if i = g.val 4 then 0 else 1 := by
  have hz : ∀ j : Fin 5, z.val j = if j = 4 then 0 else 1 := by decide
  change z.val (g.val.symm i) = _
  rw [hz]
  congr 1
  exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩

theorem orbit_in_plane (g : alternatingGroup (Fin 5))
    (h : Multiplicative.ofAdd (act g z) ∈ plane) : ∃ i : Fin 3, act g z = point i := by
  change (act g z).val 0 = (act g z).val 1 at h
  rw [orbit_word, orbit_word] at h
  generalize he : g.val 4 = j at h
  fin_cases j
  · simp at h
  · simp at h
  · refine ⟨1, Subtype.ext ?_⟩
    funext i
    rw [orbit_word, he]
    fin_cases i <;> decide
  · refine ⟨2, Subtype.ext ?_⟩
    funext i
    rw [orbit_word, he]
    fin_cases i <;> decide
  · refine ⟨0, Subtype.ext ?_⟩
    funext i
    rw [orbit_word, he]
    fin_cases i <;> decide
end BinaryPermutation.FiveCentralizerGeometry.SpanGeometry
