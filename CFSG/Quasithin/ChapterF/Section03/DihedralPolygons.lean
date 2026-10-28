module

public import Theory.GroupAction.DihedralPolygon

/-!
# The geometric conclusions of F.3.6 and F.3.7

The exponent equalities and induced cycle embeddings below follow from the
original involution and adjacency assumptions, with uniqueness of geodesics
at every distance less than `m` and `0<n`. This stronger uniqueness input
is supplied by the intended F.4.6 consumers; we do not infer it from the
insufficient distance-exactly-`m-1` condition printed in F.3.6–F.3.7.

The embeddings have the explicit alternating coordinates from the source
construction and exactly their periodic sequence as vertex set. Identifying
this set with the full union of generated-group orbits, and identifying the
faithful action quotient, remain obligations of the complete F.3.6–F.3.7
assembly. These geometry lemmas are not advertised as the complete lemmas.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.272–273, PDF pp.283–284, `refs/quasithin.pdf`.
-/

public section

namespace CFSG.Quasithin.ChapterF.Section03.DihedralPolygons

open SimpleGraph GroupAction.DihedralPolygon
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- F.3.6's exponent and concrete cycle construction under uniqueness at every
shorter distance. The vertices are the alternating rotation translates. -/
theorem lemma_F_3_6_geometry (D : BipartiteAction G Γ) {s t : G} {x l : V} {m n : ℕ}
    (hm : 1 < m) (hu : Γ.UniqueGeodesicsBelow m) (hn : 0 < n) (hnm : n ≤ m)
    (hxl : Γ.Adj x l) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsx : s • x = x) (hsl : s • l ≠ l) (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) :
    n = m ∧ ∃ e : cycleGraph (2 * m) ↪g Γ,
      (∀ i, e i = edgeVertex s t x l i.val) ∧ Set.range e = Set.range (edgeVertex s t x l) := by
  have heq := edge_exponent_eq D hu hn hnm hxl hs ht hsx hsl htl htx hx hl
  refine ⟨heq, edgeEmbedding D hm hu hn hnm hxl hs ht hsx hsl htl htx hx hl,
    fun _ => rfl, ?_⟩
  exact (edgeCircuit D hxl hs ht hsx hsl htl htx hx hl).range_embedding hm hu
    D.color D.adjacent_color (congrArg (2 * ·) heq)

/-- F.3.7's exponent and concrete cycle construction. In each four-step block
one visits `r^k*x`, `r^k*l`, `r^k*t*x`, `r^k*t*c`, where `r=t*s`. -/
theorem lemma_F_3_7_geometry (D : BipartiteAction G Γ) {s t : G} {x l c : V} {m n : ℕ}
    (hm : 4 ≤ m) (_heven : Even m) (hu : Γ.UniqueGeodesicsBelow m)
    (hn : 0 < n) (hnm : n ≤ m / 2)
    (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hcl : c ≠ l)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hsc : s • c = c) (hsx : s • x ≠ x)
    (htl : t • l = l) (htx : t • x ≠ x)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) (hc : (s * t) ^ n • c = c) :
    n = m / 2 ∧ ∃ e : cycleGraph (2 * m) ↪g Γ,
      (∀ i, e i = forkVertex s t x l c i.val) ∧ Set.range e = Set.range (forkVertex s t x l c) := by
  have heq := fork_exponent_eq D hu hn hnm hxl hxc hcl hs ht hsc hsx htl htx hx hl hc
  have hm' : 1 < m := by omega
  refine ⟨heq.1, forkEmbedding D hm' hu hn hnm hxl hxc hcl hs ht hsc hsx htl htx hx hl hc,
    fun _ => rfl, ?_⟩
  exact (forkCircuit D hxl hxc hcl hs ht hsc hsx htl htx hx hl hc).range_embedding hm' hu
    D.color D.adjacent_color (by omega)

end CFSG.Quasithin.ChapterF.Section03.DihedralPolygons
