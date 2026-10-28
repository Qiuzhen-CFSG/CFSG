module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.Configurations

/-!
# Extracting six points and lines from a twelve-cycle

The intrinsic graph is bipartite by its definition. Rotate a twelve-cycle to
start at a point, then take its even and odd vertices. Injectivity follows from
the cycle condition; both incidence clauses are actual consecutive edges.
No girth, diameter, coset identification, or apartment-conjugacy result is used.

Source context: the split G₂ geometry for Aschbacher--Smith, Theorem 0.1.2(1),
printed pp.3--4, and Theorem 0.1.1, printed pp.481--482.
-/

@[expose] public section

open Atlas.G2

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
variable {F : Type*} [Field F]

private theorem even_vertex_is_point {p : SingularPoints F} {v : GeometryVertex F}
    (w : geometryGraph.Walk (Sum.inr p) v) (n : ℕ) (hn : 2 * n ≤ w.length) :
    ∃ q : SingularPoints F, w.getVert (2 * n) = Sum.inr q := by
  induction n with
  | zero => exact ⟨p, w.getVert_zero⟩
  | succ n ih =>
    obtain ⟨q,hq⟩ := ih (by omega)
    have ha := w.adj_getVert_succ (i := 2 * n) (by omega)
    cases he : w.getVert (2 * n + 1) with
    | inr r =>
      rw [hq,he] at ha
      exact False.elim ha
    | inl L =>
      have hb := w.adj_getVert_succ (i := 2 * n + 1) (by omega)
      cases he' : w.getVert (2 * n + 1 + 1) with
      | inl M =>
        rw [he,he'] at hb
        exact False.elim hb
      | inr r =>
        exact ⟨r, rfl⟩

private theorem odd_vertex_is_line {p : SingularPoints F} {v : GeometryVertex F}
    (w : geometryGraph.Walk (Sum.inr p) v) (n : ℕ) (hn : 2 * n < w.length) :
    ∃ L : ZeroProductLine F, w.getVert (2 * n + 1) = Sum.inl L := by
  obtain ⟨q,hq⟩ := even_vertex_is_point w n hn.le
  have ha := w.adj_getVert_succ hn
  cases he : w.getVert (2 * n + 1) with
  | inr r =>
    rw [hq,he] at ha
    exact False.elim ha
  | inl L => exact ⟨L, rfl⟩

private theorem pointHexagon_of_point_cycle {p : SingularPoints F}
    (w : geometryGraph.Walk (Sum.inr p) (Sum.inr p))
    (hw : w.IsCycle) (hl : w.length = 12) :
    ∃ H : PointHexagon F,
      (∀ i, (Sum.inr (H.point i) : GeometryVertex F) ∈ w.support) ∧
      (∀ i, (Sum.inl (H.line i) : GeometryVertex F) ∈ w.support) := by
  choose q hq using fun i : Fin 6 => even_vertex_is_point w i.val (by omega)
  choose L hL using fun i : Fin 6 => odd_vertex_is_line w i.val (by omega)
  have hnext (i : Fin 6) :
      w.getVert (2 * i.val + 1 + 1) = Sum.inr (q (i + 1)) := by
    fin_cases i
    · exact hq 1
    · exact hq 2
    · exact hq 3
    · exact hq 4
    · exact hq 5
    · change w.getVert 12 = Sum.inr (q 0)
      rw [← hl, w.getVert_length]
      simpa using hq 0
  have hqi : Function.Injective q := by
    intro i j hij
    have he : w.getVert (2 * i.val) = w.getVert (2 * j.val) := by rw [hq,hq,hij]
    have hi := hw.getVert_injOn' (by dsimp; omega) (by dsimp; omega) he
    exact Fin.ext (by omega)
  have hLi : Function.Injective L := by
    intro i j hij
    have he : w.getVert (2 * i.val + 1) = w.getVert (2 * j.val + 1) := by
      rw [hL,hL,hij]
    have hi := hw.getVert_injOn' (by dsimp; omega) (by dsimp; omega) he
    exact Fin.ext (by omega)
  have hpoint (i : Fin 6) : pointOnLine (q i) (L i) := by
    have ha := w.adj_getVert_succ (i := 2 * i.val) (by omega)
    rwa [hq,hL] at ha
  have hpointNext (i : Fin 6) : pointOnLine (q (i + 1)) (L i) := by
    have ha := w.adj_getVert_succ (i := 2 * i.val + 1) (by omega)
    rwa [hL,hnext] at ha
  refine ⟨⟨q,L,hqi,hLi,hpoint,hpointNext⟩, ?_, ?_⟩
  · intro i
    change (Sum.inr (q i) : GeometryVertex F) ∈ w.support
    rw [← hq]
    exact w.getVert_mem_support _
  · intro i
    change (Sum.inl (L i) : GeometryVertex F) ∈ w.support
    rw [← hL]
    exact w.getVert_mem_support _

/-- A twelve-cycle in the actual incidence graph supplies six distinct points
and six distinct zero-product planes with all cyclic incidences. -/
theorem exists_pointHexagon_of_cycle {x : GeometryVertex F}
    (w : geometryGraph.Walk x x) (hw : w.IsCycle) (hl : w.length = 12) :
    ∃ H : PointHexagon F,
      (∀ i, (Sum.inr (H.point i) : GeometryVertex F) ∈ w.support) ∧
      (∀ i, (Sum.inl (H.line i) : GeometryVertex F) ∈ w.support) := by
  classical
  have hp : ∃ p : SingularPoints F, (Sum.inr p : GeometryVertex F) ∈ w.support := by
    cases x with
    | inr p => exact ⟨p, w.start_mem_support⟩
    | inl L =>
      have ha := w.adj_getVert_succ (i := 0) (by omega)
      rw [w.getVert_zero] at ha
      cases he : w.getVert 1 with
      | inl M =>
        rw [he] at ha
        exact False.elim ha
      | inr p => exact ⟨p, he ▸ w.getVert_mem_support 1⟩
  obtain ⟨p,hp⟩ := hp
  obtain ⟨H,hpoints,hlines⟩ := pointHexagon_of_point_cycle (w.rotate (Sum.inr p) hp)
    (hw.rotate hp) (by simpa using hl)
  refine ⟨H, ?_, ?_⟩
  · intro i
    exact (w.mem_support_rotate_iff (Sum.inr p) hp).mp (hpoints i)
  · intro i
    exact (w.mem_support_rotate_iff (Sum.inr p) hp).mp (hlines i)

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
