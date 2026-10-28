module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Recurrence

/-!
# The extra Z-containment required by backward-edge quadraticity

Conjugation inside an M-vertex stabilizer transports edge-kernel centrality
between its adjacent edges. Suppose the forward edge commutator K is contained
in the fixed core D_d at the next M-vertex. Then K centralizes its forward edge
kernel if and only if K lies in Z_d. In one direction, K is elementary abelian
and centralizes Q_d, so X_d = Z_d identifies the omega-center containment. In
the other, the Z-bound and the D-bound centralize Q_d and Ltilde_d, respectively;
these generate G_d.

The final theorem applies this equivalence to the literal failed-span
commutator and the backward indices of (4.4.4). It isolates the additional
Z-bound required by the centrality route. No proof of that bound, backward-edge
centrality, or the source recurrence is asserted here. In particular, D_d is
not silently replaced by Z_d.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the backward propagation in (4.4.4), printed p.894. The printed
containment there is in D, not Z.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching.Quadraticity
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem edge_centrality_transfer {c s t : Vertex R}
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    (h : edgeCommutator R c s ≤ centralizer (Q R s : Set (FreeAmalgam R))) :
    edgeCommutator R c t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R c hs ht
  have hgc : Stellmacher.PushingUp.AmalgamGraph.act R g c = c := hg
  have hz := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr h)
  rw [map_commutator, ← edgeCommutator_act, ← Q_act, hgc, hgt, Subgroup.map_bot] at hz
  exact commutator_eq_bot_iff_le_centralizer.mp hz

/-- For an edge lying in D_d, centrality of its edge kernel is equivalent to
containment in Z_d. The implication back uses G_d = Ltilde_d Q_d. -/
theorem forward_centrality_iff_le_Z (common : CommonFacts R source geometry)
    {c d t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hct : Adjacent R c t) (hdt : Adjacent R d t)
    {K : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hfixed : K ≤ fixedCore R d) :
    K ≤ centralizer (Q R t : Set (FreeAmalgam R)) ↔ K ≤ Z R d := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hKZ : K ≤ Z R c := by
    rw [hforward]
    exact (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) c t hc hct).trans (U_le_Z R c)
  constructor
  · intro h x hx
    rw [← common.X_eq_Z d hd]
    change x ∈ omegaCenter (Q R d)
    let := geometry.Z_elementary (by have := common.large_distance; omega) c hc
    exact mem_omegaCenter_iff.mpr ⟨(hfixed hx).1,
      elemPow_eq_one_of_isElementaryAbelian x (hKZ hx),
      fun y hy => h hx y (Q_le_adjacent_h R ht hdt hy)⟩
  · intro h
    have hQ : K ≤ centralizer (Q R d : Set (FreeAmalgam R)) :=
      h.trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd))
    have hG : K ≤ centralizer (stabilizer R d : Set (FreeAmalgam R)) := by
      apply le_centralizer_iff.mp
      rw [← source.local_generation d hd]
      exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right))
        (le_centralizer_iff.mp hQ)
    exact hG.trans (centralizer_le (show Q R t ≤ stabilizer R d from
      fun _ hx => hx.2 d (adjacent_symm R hdt)))

/-- The exact pointwise backward-edge target reduces to an additional Z-bound
at the forward M-vertex. The source's D-bound alone is retained, not strengthened. -/
theorem backward_centrality_iff_le_forward_Z (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (hforward : failedSpanCommutator p g = edgeCommutator R
      (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)))
    (hfixed : failedSpanCommutator p g ≤ fixedCore R
      (p.walk.getVert (p.walk.length - 4 * n + 2))) :
    edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      centralizer (Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) :
        Set (FreeAmalgam R)) ↔
    failedSpanCommutator p g ≤ Z R (p.walk.getVert (p.walk.length - 4 * n + 2)) := by
  have heven : Even (p.walk.length - 4 * n) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [← p.length_eq_b, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  have hc : color R (p.walk.getVert (p.walk.length - 4 * n)) = false :=
    (p.vertex_color (by omega)).mpr heven
  have hd : color R (p.walk.getVert (p.walk.length - 4 * n + 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hs : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n - 1)) := by
    apply adjacent_symm R
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 4 * n - 1) (by omega)
    rw [show p.walk.length - 4 * n - 1 + 1 = p.walk.length - 4 * n by omega] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have ht : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hdt : Adjacent R (p.walk.getVert (p.walk.length - 4 * n + 2))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) := by
    apply adjacent_symm R
    exact (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  rw [← forward_centrality_iff_le_Z common hc hd ht hdt hforward hfixed, hforward]
  exact ⟨edge_centrality_transfer hs ht, edge_centrality_transfer ht hs⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching.Quadraticity
