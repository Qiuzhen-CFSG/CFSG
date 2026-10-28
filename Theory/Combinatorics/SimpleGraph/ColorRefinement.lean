module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Kernel-checkable neighbor-color rigidity

A graph automorphism permutes each actual neighbor list. Consequently it
preserves every deterministic refinement formed from a vertex color and a
symmetric polynomial sum of its neighbor colors. A supplied finite refinement
sequence whose final colors are distinct therefore proves rigidity of the
automorphisms preserving the initial colors. Collisions in intermediate
polynomial signatures are harmless: only the final injectivity is required.

The binary Ree building application checks the concrete refinement equations
and final distinctness separately, retaining the original incidence graph.
-/

@[expose] public section
namespace SimpleGraph.ColorRefinement
variable {V : Type*} (Γ : SimpleGraph V)

structure NeighborLists where
  neighbors : V → List V
  nodup : ∀ v, (neighbors v).Nodup
  mem_iff : ∀ v w, w ∈ neighbors v ↔ Γ.Adj v w

variable {Γ}

def moment (c : ℕ) : ℕ :=
  let x := c+1
  x+32768*x^2+4398046511104*x^3

def signature (N : NeighborLists Γ) (c : V → ℕ) (v : V) : ℕ :=
  c v+1 + 8192 * ((N.neighbors v).map (fun w => moment (c w))).sum

lemma neighbors_perm (N : NeighborLists Γ) (a : (Γ ≃g Γ)) (v : V) :
    (N.neighbors (a v)).Perm ((N.neighbors v).map a) := by
  apply (List.perm_ext_iff_of_nodup (N.nodup _) ((N.nodup v).map a.injective)).mpr
  intro w
  rw [N.mem_iff, List.mem_map]
  constructor
  · intro hw
    refine ⟨a.symm w, ?_, a.apply_symm_apply w⟩
    rw [N.mem_iff]
    have hh := a.symm.toHom.map_adj hw
    change Γ.Adj (a.symm (a v)) (a.symm w) at hh
    simpa only [a.symm_apply_apply] using hh
  · rintro ⟨x,hx,rfl⟩
    exact a.toHom.map_adj ((N.mem_iff _ _).mp hx)

lemma signature_invariant (N : NeighborLists Γ) (a : (Γ ≃g Γ)) (c : V → ℕ)
    (hc : ∀ v, c (a v) = c v) (v : V) : signature N c (a v) = signature N c v := by
  unfold signature
  rw [hc]
  congr 2
  have hh := ((neighbors_perm N a v).map (fun w => moment (c w))).sum_eq
  simpa only [List.map_map, Function.comp_def, hc] using hh

lemma refinement_invariant (N : NeighborLists Γ) (a : (Γ ≃g Γ)) (c d : V → ℕ)
    (f : ℕ → ℕ) (hd : ∀ v, d v = f (signature N c v))
    (hc : ∀ v, c (a v) = c v) : ∀ v, d (a v) = d v := by
  intro v
  rw [hd, hd, signature_invariant N a c hc]

/-- A finite sequence of certified neighbor refinements ending in distinct
colors determines every automorphism fixing the initial colors. -/
theorem eq_refl_of_refinement (N : NeighborLists Γ) (a : (Γ ≃g Γ))
    (n : ℕ) (c : ℕ → V → ℕ) (f : ℕ → ℕ → ℕ)
    (hstep : ∀ k < n, ∀ v, c (k+1) v = f k (signature N (c k) v))
    (hinj : Function.Injective (c n))
    (hinit : ∀ v, c 0 (a v) = c 0 v) : a = SimpleGraph.Iso.refl := by
  have hpres : ∀ k, k ≤ n → ∀ v, c k (a v) = c k v := by
    intro k
    induction k with
    | zero => intro _; exact hinit
    | succ k ih =>
      intro hk
      exact refinement_invariant N a (c k) (c (k+1)) (f k)
        (hstep k (Nat.lt_of_succ_le hk)) (ih (Nat.le_of_succ_le hk))
  ext v
  exact hinj (hpres n le_rfl v)
end SimpleGraph.ColorRefinement
