module

public import Theory.GroupAction.DihedralPolygon.Geodesics
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Conj

/-!
# Involution constructions of embedded polygons

Two involutions fixing alternate ends of an edge give the sequence
`r^k*x, r^k*l`, where `r=t*s`. In the three-orbit variant, the four-step
sequence is `r^k*x, r^k*l, r^k*t*x, r^k*t*c`. The fixed-point assumptions
give periods `2*n` and `4*n`, respectively; the moving-point assumptions
exclude backtracking. The short-geodesic bound forces these periods to
be `2*m` and produces induced embeddings of the actual cycle graph.

These are the geometric constructions in Aschbacher–Smith F.3.6–F.3.7,
printed pp.272–273 of the combined manuscript (1 March 2004). We retain
the required positivity of `n` and use uniqueness at all distances below
`m`, the hypothesis available to the intended F.4 consumers. This module
does not yet identify the generated group's action kernel or its quotient.
The orbit-support and group identifications are separate assembly obligations.
-/

@[expose] public section

namespace GroupAction.DihedralPolygon
open SimpleGraph
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- An action by graph automorphisms preserving a specified bipartition. -/
structure BipartiteAction (G : Type*) [Group G] {V : Type*} [MulAction G V]
    (Γ : SimpleGraph V) where
  color : V → Bool
  adjacent_color : ∀ {x y}, Γ.Adj x y → color x ≠ color y
  smul_adj : ∀ (g : G) {x y}, Γ.Adj x y → Γ.Adj (g • x) (g • y)
  smul_color : ∀ (g : G) (x : V), color (g • x) = color x

/-- The alternating two-orbit sequence, using the left-action rotation `t*s`. -/
def edgeVertex (s t : G) (x l : V) (i : ℕ) : V :=
  (t * s) ^ (i / 2) • (if i % 2 = 0 then x else l)

private theorem edgeVertex_step (D : BipartiteAction G Γ) {s t : G} {x l : V}
    (hxl : Γ.Adj x l) (hsx : s • x = x) (htl : t • l = l) (i : ℕ) :
    Γ.Adj (edgeVertex s t x l i) (edgeVertex s t x l (i + 1)) := by
  by_cases hi : i % 2 = 0
  · have hj : (i + 1) % 2 ≠ 0 := by omega
    have hd : (i + 1) / 2 = i / 2 := by omega
    simpa only [edgeVertex, if_pos hi, if_neg hj, hd] using D.smul_adj ((t * s) ^ (i / 2)) hxl
  · have hj : (i + 1) % 2 = 0 := by omega
    have hd : (i + 1) / 2 = i / 2 + 1 := by omega
    have h : Γ.Adj l ((t * s) • x) := by simpa only [mul_smul, hsx, htl] using D.smul_adj t hxl.symm
    simpa only [edgeVertex, if_neg hi, if_pos hj, hd, pow_succ, mul_smul] using
      D.smul_adj ((t * s) ^ (i / 2)) h

private theorem edgeVertex_noBacktrack {s t : G} {x l : V}
    (ht : t ^ 2 = 1) (hsx : s • x = x) (hsl : s • l ≠ l)
    (htl : t • l = l) (htx : t • x ≠ x) (i : ℕ) :
    edgeVertex s t x l i ≠ edgeVertex s t x l (i + 2) := by
  have hrx : (t * s) • x ≠ x := by simpa only [mul_smul, hsx] using htx
  have hrl : (t * s) • l ≠ l := by
    intro h
    apply hsl
    have h' := congrArg (fun v => t • v) h
    simpa only [mul_smul, ← mul_smul t t, ← pow_two, ht, one_smul, htl] using h'
  have hd : (i + 2) / 2 = i / 2 + 1 := by omega
  have hm : (i + 2) % 2 = i % 2 := by omega
  unfold edgeVertex
  rw [hd, hm, pow_succ, mul_smul]
  intro h
  have he := (MulAction.injective ((t * s) ^ (i / 2))) h
  split_ifs at he with hi
  · exact hrx he.symm
  · exact hrl he.symm

/-- A fixed power of `s*t` also fixes under the inverse rotation `t*s`. -/
theorem inverse_rotation_fixed {s t : G} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    {n : ℕ} {v : V} (hv : (s * t) ^ n • v = v) : (t * s) ^ n • v = v := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have h := congrArg (fun w => ((s * t) ^ n)⁻¹ • w) hv
  have hfix : ((s * t) ^ n)⁻¹ • v = v := by simpa only [inv_smul_smul] using h.symm
  simpa only [← inv_pow, mul_inv_rev, hsi, hti] using hfix

private theorem edgeVertex_periodic {s t : G} {x l : V} {n : ℕ}
    (hx : (t * s) ^ n • x = x) (hl : (t * s) ^ n • l = l) (i : ℕ) :
    edgeVertex s t x l (i + 2 * n) = edgeVertex s t x l i := by
  have hd : (i + 2 * n) / 2 = i / 2 + n := by omega
  have hm : (i + 2 * n) % 2 = i % 2 := by omega
  simp only [edgeVertex, hd, hm, pow_add, mul_smul]
  split_ifs <;> simp only [hx, hl]

/-- The two involutions construct a periodic nonbacktracking circuit of length `2*n`.
No uniqueness or girth assumption is used in this construction. -/
def edgeCircuit (D : BipartiteAction G Γ) {s t : G} {x l : V} {n : ℕ}
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) :
    Γ.NonbacktrackingCircuit (2 * n) where
  vertex := edgeVertex s t x l
  adjacent := by exact edgeVertex_step D hxl hsx htl
  nonbacktracking := by exact edgeVertex_noBacktrack ht hsx hsl htl htx
  periodic := by exact edgeVertex_periodic (inverse_rotation_fixed hs ht hx) (inverse_rotation_fixed hs ht hl)

/-- The numerical conclusion of F.3.6 with the actual short-geodesic hypothesis. -/
theorem edge_exponent_eq (D : BipartiteAction G Γ) {s t : G} {x l : V} {m n : ℕ}
    (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m)
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) : n = m := by
  have h := (edgeCircuit D hxl hs ht hsx hsl htl htx hx hl).length_ge hu D.color D.adjacent_color (by omega)
  omega

/-- The concrete induced `2*m`-cycle in the first involution construction. -/
def edgeEmbedding (D : BipartiteAction G Γ) {s t : G} {x l : V} {m n : ℕ}
    (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m)
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) :
    cycleGraph (2 * m) ↪g Γ :=
  (edgeCircuit D hxl hs ht hsx hsl htl htx hx hl).embedding hm hu D.color D.adjacent_color
    (congrArg (2 * ·) (edge_exponent_eq D hu hn hnm hxl hs ht hsx hsl htl htx hx hl))

end GroupAction.DihedralPolygon
namespace GroupAction.DihedralPolygon
open SimpleGraph
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- The four-step sequence for the three-orbit construction. -/
def forkVertex (s t : G) (x l c : V) (i : ℕ) : V :=
  (t * s) ^ (i / 4) •
    (if i % 4 = 0 then x else if i % 4 = 1 then l else if i % 4 = 2 then t • x else t • c)

private theorem forkVertex_step (D : BipartiteAction G Γ) {s t : G} {x l c : V}
    (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hsc : s • c = c) (htl : t • l = l)
    (i : ℕ) : Γ.Adj (forkVertex s t x l c i) (forkVertex s t x l c (i + 1)) := by
  have hi : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · have hj : (i + 1) % 4 = 1 := by omega
    have hd : (i + 1) / 4 = i / 4 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte] using D.smul_adj ((t * s) ^ (i / 4)) hxl
  · have hj : (i + 1) % 4 = 2 := by omega
    have hd : (i + 1) / 4 = i / 4 := by omega
    have h : Γ.Adj l (t • x) := by simpa only [htl] using D.smul_adj t hxl.symm
    simpa [forkVertex, hi, hj, hd, ↓reduceIte] using D.smul_adj ((t * s) ^ (i / 4)) h
  · have hj : (i + 1) % 4 = 3 := by omega
    have hd : (i + 1) / 4 = i / 4 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte] using D.smul_adj ((t * s) ^ (i / 4)) (D.smul_adj t hxc)
  · have hj : (i + 1) % 4 = 0 := by omega
    have hd : (i + 1) / 4 = i / 4 + 1 := by omega
    have h : Γ.Adj (t • c) ((t * s) • x) := by simpa only [mul_smul, hsc] using D.smul_adj (t * s) hxc.symm
    simpa [forkVertex, hi, hj, hd, ↓reduceIte, pow_succ, mul_smul] using
      D.smul_adj ((t * s) ^ (i / 4)) h

private theorem forkVertex_noBacktrack {s t : G} {x l c : V}
    (hcl : c ≠ l) (hsx : s • x ≠ x) (hsc : s • c = c)
    (htl : t • l = l) (htx : t • x ≠ x) (i : ℕ) :
    forkVertex s t x l c i ≠ forkVertex s t x l c (i + 2) := by
  have hlc : l ≠ t • c := by
    intro h
    apply hcl
    exact (MulAction.injective t) (h.symm.trans htl.symm)
  have hcs : c ≠ s • l := by
    intro h
    apply hcl
    exact (MulAction.injective s) (hsc.trans h)
  have hi : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · have hj : (i + 2) % 4 = 2 := by omega
    have hd : (i + 2) / 4 = i / 4 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte, ne_eq, (MulAction.injective _).eq_iff] using htx.symm
  · have hj : (i + 2) % 4 = 3 := by omega
    have hd : (i + 2) / 4 = i / 4 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte, ne_eq, (MulAction.injective _).eq_iff] using hlc
  · have hj : (i + 2) % 4 = 0 := by omega
    have hd : (i + 2) / 4 = i / 4 + 1 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte, pow_succ, mul_smul, ne_eq,
      (MulAction.injective _).eq_iff] using hsx.symm
  · have hj : (i + 2) % 4 = 1 := by omega
    have hd : (i + 2) / 4 = i / 4 + 1 := by omega
    simpa [forkVertex, hi, hj, hd, ↓reduceIte, pow_succ, mul_smul, ne_eq,
      (MulAction.injective _).eq_iff] using hcs

private theorem rotation_pow_mul_t {s t : G} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (n : ℕ) :
    (t * s) ^ n * t = t * ((t * s) ^ n)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have htt : t * t = 1 := by simpa only [pow_two] using ht
  have hc : t * (t * s) * t⁻¹ = (t * s)⁻¹ := by
    simp only [mul_inv_rev, hsi, hti, ← mul_assoc, htt, one_mul]
  have hp : t * (t * s) ^ n * t⁻¹ = ((t * s) ^ n)⁻¹ := by
    rw [← conj_pow, hc, inv_pow]
  calc
    (t * s) ^ n * t = t * (t * (t * s) ^ n * t⁻¹) := by
      simp only [hti, ← mul_assoc, htt, one_mul]
    _ = t * ((t * s) ^ n)⁻¹ := by rw [hp]

private theorem rotation_fixed_translate {s t : G} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    {n : ℕ} {v : V} (hv : (t * s) ^ n • v = v) :
    (t * s) ^ n • (t • v) = t • v := by
  have hi : ((t * s) ^ n)⁻¹ • v = v := by
    simpa only [inv_smul_smul] using (congrArg (fun w => ((t * s) ^ n)⁻¹ • w) hv).symm
  rw [← mul_smul, rotation_pow_mul_t hs ht, mul_smul, hi]

private theorem forkVertex_periodic {s t : G} {x l c : V} {n : ℕ}
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hx : (t * s) ^ n • x = x) (hl : (t * s) ^ n • l = l) (hc : (t * s) ^ n • c = c)
    (i : ℕ) : forkVertex s t x l c (i + 4 * n) = forkVertex s t x l c i := by
  have hd : (i + 4 * n) / 4 = i / 4 + n := by omega
  have hm : (i + 4 * n) % 4 = i % 4 := by omega
  simp only [forkVertex, hd, hm, pow_add, mul_smul]
  split_ifs <;> simp only [hx, hl, rotation_fixed_translate hs ht hx, rotation_fixed_translate hs ht hc]

/-- The three-orbit involution construction before invoking the girth bound. -/
def forkCircuit (D : BipartiteAction G Γ) {s t : G} {x l c : V} {n : ℕ}
    (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hcl : c ≠ l)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hsc : s • c = c) (hsx : s • x ≠ x)
    (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) (hc : (s * t) ^ n • c = c) :
    Γ.NonbacktrackingCircuit (4 * n) where
  vertex := forkVertex s t x l c
  adjacent := by exact forkVertex_step D hxl hxc hsc htl
  nonbacktracking := by exact forkVertex_noBacktrack hcl hsx hsc htl htx
  periodic := by
    exact forkVertex_periodic hs ht (inverse_rotation_fixed hs ht hx)
      (inverse_rotation_fixed hs ht hl) (inverse_rotation_fixed hs ht hc)

/-- The numerical conclusion of F.3.7, using uniqueness at all distances below `m`. -/
theorem fork_exponent_eq (D : BipartiteAction G Γ) {s t : G} {x l c : V} {m n : ℕ}
    (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m / 2)
    (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hcl : c ≠ l)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hsc : s • c = c) (hsx : s • x ≠ x)
    (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) (hc : (s * t) ^ n • c = c) :
    n = m / 2 ∧ 2 * n = m := by
  have h := (forkCircuit D hxl hxc hcl hs ht hsc hsx htl htx hx hl hc).length_ge hu D.color D.adjacent_color (by omega)
  omega

/-- The concrete induced `2*m`-cycle in the second involution construction. -/
def forkEmbedding (D : BipartiteAction G Γ) {s t : G} {x l c : V} {m n : ℕ}
    (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m / 2)
    (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hcl : c ≠ l)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hsc : s • c = c) (hsx : s • x ≠ x)
    (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) (hc : (s * t) ^ n • c = c) :
    cycleGraph (2 * m) ↪g Γ :=
  (forkCircuit D hxl hxc hcl hs ht hsc hsx htl htx hx hl hc).embedding hm hu D.color D.adjacent_color (by
    have h := (fork_exponent_eq D hu hn hnm hxl hxc hcl hs ht hsc hsx htl htx hx hl hc).2
    omega)

end GroupAction.DihedralPolygon
