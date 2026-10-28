module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Collinearity in the split octonion hexagon

The incidence graph joins singular projective points to zero-product planes.
Its girth bound implies that two distinct paths of combined length less than
12 cannot have the same endpoints. Consequently, any four distinct points
forming a quadrangle in the point collinearity graph lie on one geometric
line. Over the binary field a line has only three points, ruling out that
quadrangle and every collinearity cycle of length four.

Triangles on one line are allowed. The binary-field restriction on the final
conclusion is essential: over a larger field four points of a single line
already form a collinearity four-cycle.

This proves the concrete geometry assertion used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
Lemma 14.7.55(7), printed p.1066, and the last paragraph of Theorem 14.7.53,
printed p.1069. Identifying an arbitrary module geometry with this model is a
separate representation-theoretic obligation. The imported octonion model
and its girth proof retain their ATLAS attribution and license.
-/

@[expose] public section

open SimpleGraph
open Atlas.G2
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

private theorem short_paths_eq {x y : GeometryVertex F}
    {p q : geometryGraph.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 12) : p = q := by
  by_contra hne
  obtain ⟨z, _, _, c, hc, hl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := geometryGraph_girth_bound z c hc
  omega

/-- The point collinearity graph of the intrinsic octonion geometry. -/
def collinearityGraph : SimpleGraph (SingularPoints F) where
  Adj p q := p ≠ q ∧ ∃ L : ZeroProductLine F, pointOnLine p L ∧ pointOnLine q L
  symm := ⟨fun _ _ ⟨h, L, hp, hq⟩ => ⟨h.symm, L, hq, hp⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def viaLine {p q : SingularPoints F} {L : ZeroProductLine F}
    (hp : pointOnLine p L) (hq : pointOnLine q L) :
    geometryGraph.Walk (Sum.inr p) (Sum.inr q) :=
  .cons (v := Sum.inl L) hp (.cons (v := Sum.inr q) hq .nil)

private theorem viaLine_isPath {p q : SingularPoints F} {L : ZeroProductLine F}
    (hpq : p ≠ q) (hp : pointOnLine p L) (hq : pointOnLine q L) :
    (viaLine hp hq).IsPath := by
  apply Walk.IsPath.mk'
  change [Sum.inr p, Sum.inl L, Sum.inr q].Nodup
  simp [hpq]

private def viaTwoLines {p q r : SingularPoints F} {L M : ZeroProductLine F}
    (hp : pointOnLine p L) (hrL : pointOnLine r L)
    (hrM : pointOnLine r M) (hq : pointOnLine q M) :
    geometryGraph.Walk (Sum.inr p) (Sum.inr q) :=
  .cons (v := Sum.inl L) hp (.cons (v := Sum.inr r) hrL
    (.cons (v := Sum.inl M) hrM (.cons (v := Sum.inr q) hq .nil)))

private theorem viaTwoLines_isPath {p q r : SingularPoints F} {L M : ZeroProductLine F}
    (hpq : p ≠ q) (hpr : p ≠ r) (hrq : r ≠ q) (hLM : L ≠ M)
    (hp : pointOnLine p L) (hrL : pointOnLine r L)
    (hrM : pointOnLine r M) (hq : pointOnLine q M) :
    (viaTwoLines hp hrL hrM hq).IsPath := by
  apply Walk.IsPath.mk'
  change [Sum.inr p, Sum.inl L, Sum.inr r, Sum.inl M, Sum.inr q].Nodup
  simp [hpq, hpr, hrq, hLM]

/-- Any triangle of collinear points lies on one geometric line. -/
theorem pointOnLine_of_adjacent_pair {p q r : SingularPoints F} {L : ZeroProductLine F}
    (hpq : p ≠ q) (hp : pointOnLine p L) (hq : pointOnLine q L)
    (hpr : collinearityGraph.Adj p r) (hqr : collinearityGraph.Adj q r) :
    pointOnLine r L := by
  obtain ⟨hpr, M, hpM, hrM⟩ := hpr
  obtain ⟨hqr, N, hqN, hrN⟩ := hqr
  by_cases hMN : M = N
  · subst N
    have hLM := metric_line_unique hpq hp hq hpM hqN
    simpa only [hLM] using hrM
  · have he := short_paths_eq (viaLine_isPath hpq hp hq)
      (viaTwoLines_isPath hpq hpr hqr.symm hMN hpM hrM hrN hqN)
      (by change (6 : ℕ) < 12; decide)
    have hh := congrArg Walk.length he
    have : (2 : ℕ) = 4 := hh
    contradiction

/-- Four distinct points forming a quadrangle must all lie on one line.
This conclusion holds over every field; it does not assert that the
collinearity graph is triangle-free. -/
theorem common_neighbors_on_one_line {p q r s : SingularPoints F}
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hpr : collinearityGraph.Adj p r) (hqr : collinearityGraph.Adj q r)
    (hps : collinearityGraph.Adj p s) (hqs : collinearityGraph.Adj q s) :
    ∃ L : ZeroProductLine F,
      pointOnLine p L ∧ pointOnLine q L ∧ pointOnLine r L ∧ pointOnLine s L := by
  obtain ⟨hpr', L, hpL, hrL⟩ := hpr
  obtain ⟨hqr', M, hqM, hrM⟩ := hqr
  by_cases hLM : L = M
  · subst M
    exact ⟨L, hpL, hqM, hrL, pointOnLine_of_adjacent_pair hpq hpL hqM hps hqs⟩
  · obtain ⟨hps', N, hpN, hsN⟩ := hps
    obtain ⟨hqs', O, hqO, hsO⟩ := hqs
    by_cases hNO : N = O
    · subst O
      have he := short_paths_eq (viaLine_isPath hpq hpN hqO)
        (viaTwoLines_isPath hpq hpr' hqr'.symm hLM hpL hrL hrM hqM)
        (by change (6 : ℕ) < 12; decide)
      have hh := congrArg Walk.length he
      have : (2 : ℕ) = 4 := hh
      contradiction
    · have he := short_paths_eq
        (viaTwoLines_isPath hpq hpr' hqr'.symm hLM hpL hrL hrM hqM)
        (viaTwoLines_isPath hpq hps' hqs'.symm hNO hpN hsN hsO hqO)
        (by change (8 : ℕ) < 12; decide)
      have hh := congrArg (fun w => w.getVert 2) he
      have heq : r = s := Sum.inr.inj hh
      exact (hrs heq).elim

/-- A binary geometric line has at most three singular points. -/
theorem binary_line_card_le_three (L : ZeroProductLine (ZMod 2)) :
    Nat.card {p : SingularPoints (ZMod 2) // pointOnLine p L} ≤ 3 := by
  let f : {p : SingularPoints (ZMod 2) // pointOnLine p L} →
      Projectivization (ZMod 2) L.val := fun p =>
    Projectivization.mk (ZMod 2)
      ⟨p.val.val.rep, (pointOnLine_iff p.val L).mp p.property⟩
      (fun h => p.val.val.rep_nonzero (congrArg Subtype.val h))
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (Projectivization.map L.val.subtype Subtype.val_injective) h
    change Projectivization.mk (ZMod 2) p.val.val.rep _ =
      Projectivization.mk (ZMod 2) q.val.val.rep _ at hh
    simpa only [Projectivization.mk_rep] using hh
  have hc := Nat.card_le_card_of_injective f hf
  have hcard := Projectivization.card_of_finrank_two (ZMod 2) L.val L.property.1
  norm_num [Nat.card_eq_fintype_card] at hcard
  exact hcard ▸ hc

/-- Two distinct binary singular points have at most one common neighbour. -/
theorem binary_common_neighbor_unique {p q r s : SingularPoints (ZMod 2)}
    (hpq : p ≠ q)
    (hpr : collinearityGraph.Adj p r) (hqr : collinearityGraph.Adj q r)
    (hps : collinearityGraph.Adj p s) (hqs : collinearityGraph.Adj q s) : r = s := by
  by_contra hrs
  obtain ⟨L, hp, hq, hr, hs⟩ := common_neighbors_on_one_line hpq hrs hpr hqr hps hqs
  let f : Fin 4 → {t : SingularPoints (ZMod 2) // pointOnLine t L} :=
    ![⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hpr' := hpr.1
    have hqr' := hqr.1
    have hps' := hps.1
    have hqs' := hqs.1
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hc := Nat.card_le_card_of_injective f hf
  have hcard := binary_line_card_le_three L
  simp only [Nat.card_fin] at hc
  omega


/-- There is no four-cycle in the binary point collinearity graph. -/
theorem binary_collinearity_no_four_cycle (p : SingularPoints (ZMod 2))
    (w : collinearityGraph.Walk p p) (hw : w.IsCycle) : w.length ≠ 4 := by
  intro hl
  have hinj := hw.getVert_injOn'
  have h02 : w.getVert 0 ≠ w.getVert 2 := by
    intro he
    have : (0 : ℕ) = 2 := hinj (by simp [hl]) (by simp [hl]) he
    contradiction
  have h13 : w.getVert 1 ≠ w.getVert 3 := by
    intro he
    have : (1 : ℕ) = 3 := hinj (by simp [hl]) (by simp [hl]) he
    contradiction
  have h01 := w.adj_getVert_succ (i := 0) (by omega)
  have h12 := w.adj_getVert_succ (i := 1) (by omega)
  have h23 := w.adj_getVert_succ (i := 2) (by omega)
  have h30 : collinearityGraph.Adj (w.getVert 3) (w.getVert 0) := by
    have h34 := w.adj_getVert_succ (i := 3) (by omega)
    change collinearityGraph.Adj (w.getVert 3) (w.getVert 4) at h34
    rw [← hl, Walk.getVert_length] at h34
    rw [Walk.getVert_zero]
    exact h34
  exact h13 (binary_common_neighbor_unique h02 h01 h12.symm h30.symm h23)

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
