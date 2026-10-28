module
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Contracts

/-!
# Extracting the connected incidence graph from a decomposition matrix

A nonnegative integer column of squared norm two consists of two distinct
entries equal to one. If each nonempty proper set of rows has a column
meeting both sides, its endpoint graph is connected: a reachable component
would otherwise give a separating row set.

These are the finite combinatorial steps in Feit VII.6.4. The hypotheses
are intended to be supplied by the cyclic column theorem VII.2.13--15 and
the block indecomposability assertion I.17.9; neither assertion is assumed
to hold for arbitrary matrices.
-/

public section
noncomputable section
open scoped BigOperators Classical
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence

/-- An integral nonnegative column of squared norm two has exactly two ones. -/
theorem exists_endpoints_of_sum_sq_eq_two {V : Type*} [Fintype V]
    (f : V → ℕ) (h : ∑ v, f v ^ 2 = 2) :
    ∃ l r : V, l ≠ r ∧ ∀ v, f v = if v = l ∨ v = r then 1 else 0 := by
  have hsmall (v : V) : f v = 0 ∨ f v = 1 := by
    have hv : f v ^ 2 ≤ 2 := by
      calc
        f v ^ 2 ≤ ∑ w, f w ^ 2 :=
          Finset.single_le_sum (f := fun w => f w ^ 2)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        _ = 2 := h
    have : f v ≤ 1 := by nlinarith
    omega
  let s : Finset V := Finset.univ.filter fun v => f v ≠ 0
  have hf (v : V) : f v ^ 2 = if f v ≠ 0 then 1 else 0 := by
    rcases hsmall v with hv | hv <;> simp [hv]
  have hs : s.card = 2 := calc
    s.card = ∑ v, if f v ≠ 0 then 1 else 0 := by
      dsimp [s]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ v, f v ^ 2 := Finset.sum_congr rfl fun v _ => (hf v).symm
    _ = 2 := h
  obtain ⟨l, r, hlr, hsr⟩ := Finset.card_eq_two.mp hs
  refine ⟨l, r, hlr, ?_⟩
  intro v
  have hv : f v ≠ 0 ↔ v = l ∨ v = r := by
    have hs' : v ∈ s ↔ v = l ∨ v = r := by simp [hsr]
    simpa [s] using hs'
  rcases hsmall v with hzero | hone
  · simp [hzero, ← hv]
  · have hmem := hv.mp (by omega)
    simp [hone, hmem]

/-- If every proper nonempty row set has a column meeting both sides,
its two-endpoint graph is connected. -/
theorem endpointGraph_connected_of_crossing {V : Type*} [Fintype V] [Nonempty V]
    {n : ℕ} (f : V → Fin n → ℕ) (left right : Fin n → V)
    (hne : ∀ e, left e ≠ right e)
    (hf : ∀ v e, f v e = if v = left e ∨ v = right e then 1 else 0)
    (hcross : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      ∃ e v w, v ∈ S ∧ w ∉ S ∧ f v e ≠ 0 ∧ f w e ≠ 0) :
    (endpointGraph left right).Connected := by
  let H := endpointGraph left right
  refine ⟨?_⟩
  intro u z
  by_contra huz
  let S : Finset V := Finset.univ.filter fun v => H.Reachable u v
  have hu : u ∈ S := by simp [S]
  have hz : z ∉ S := by simpa [S] using huz
  have hS : S ≠ Finset.univ := by
    intro hS
    exact hz (hS ▸ Finset.mem_univ z)
  obtain ⟨e, v, w, hv, hw, hve, hwe⟩ := hcross S ⟨u, hu⟩ hS
  have hev : v = left e ∨ v = right e := by
    by_contra h
    simp [hf, h] at hve
  have hew : w = left e ∨ w = right e := by
    by_contra h
    simp [hf, h] at hwe
  have hadj : H.Adj (left e) (right e) := ⟨⟨e, rfl⟩, hne e⟩
  have hreach : H.Reachable v w := by
    rcases hev with rfl | rfl <;> rcases hew with rfl | rfl
    · exact .rfl
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact .rfl
  exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w,
    (Finset.mem_filter.mp hv).2.trans hreach⟩)

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
