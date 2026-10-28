module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges

/-!
# Comparing the predecessor commutator with the starting edge

The trapped radius V_a lies in Q_c, where c is two before the critical
endpoint. Consequently Z_c centralizes every Z_e with d(e,a) = 2.
Critical minimality places Z_c in G_e, so the exact local centralizer
identifies Z_c as a subgroup of Q_e.

For each reverse-moving generator V_e of W(t), the favorable bound in
Q_d puts V_e in G_c. The decomposition V_e = Vcirc_e V_t then reduces
its commutator with Z_c to the moving factor: V_t lies in V_a and hence
centralizes Z_c. This gives [V_e,Z_c] ≤ H_e = [Z_a,Q_t]. A commutator
preimage passes the comparison to the entire span W(t).

This proves the containment underlying the assertion
N = [W(t),Z_c] = [Z_a,Q_t] ∩ Z_beta. The intersection-line identification
and the subsequent change of edge belong to Selection.Assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.7)(i), printed pp.887--888, especially “As above” on p.888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem predecessor_Z_le_kernel (source : LocalSource L R)
    (p : Counterexample geometry) (e : Vertex R)
    (he : (cosetGraph R).dist e p.a = 2) : Z R p.c ≤ Q R e := by
  have hec : color R e = false :=
    (color_eq_of_dist_even R e p.a (he.symm ▸ (by decide : Even 2))).trans p.color_a
  have hZe : Z R e ≤ Q R p.c :=
    (show Z R e ≤ V R p.a from le_iSup_of_le e (le_iSup_of_le he.le le_rfl)).trans
      p.trapped
  rw [← source.C_eq_Q geometry.radical_ne_bot e hec]
  apply le_inf
  · apply Z_le_stabilizer_of_dist_le p.c (geometry.exists_critical p.c p.before_color)
    rw [geometry.distance_constant p.c p.before_color]
    change (cosetGraph R).dist p.c e ≤ geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := p.c) (v := p.a) (w := e)
    have hpath := p.before.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := p.c)] at hpath
    rw [SimpleGraph.dist_comm (u := p.a) (v := e), he] at htri
    omega
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.c p.before_color)).trans (centralizer_le hZe)

private theorem generator_predecessor_commutator_le_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (t e : Vertex R) (hat : Adjacent R p.a t) (het : Adjacent R e t)
    (hea : p.a ∈ movingNeighbors geometry e)
    (hlocal : V R e ≤ stabilizer R p.c) :
    ⁅V R e, Z R p.c⁆ ≤ edgeDisplacement p.a t := by
  have hec : color R e = false :=
    (color_eq_of_dist_even R e p.a (hea.1.symm ▸ (by decide : Even 2))).trans p.color_a
  have hcentral : V R t ≤ centralizer (Z R p.c : Set (FreeAmalgam R)) :=
    ((PairingControl.Geometry.LocalProducts.edge_radius_le_radius p.color_a hat).trans
      p.trapped).trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.c p.before_color)))
  have heq : ⁅Z R p.c, Vcirc R e⁆ = ⁅Z R p.c, V R e⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (PairingControl.Geometry.LocalProducts.radius_eq_moving_sup_edge
        source hec het).symm) hcentral
      ((PairingControl.Geometry.Vcirc_le_V e).trans (hlocal.trans (Z_normalized R p.c)))
  have hbound : ⁅V R e, Z R p.c⁆ ≤ H R e := by
    rw [commutator_comm, ← heq, commutator_comm]
    exact commutator_mono le_rfl (predecessor_Z_le_kernel source p e hea.1)
  exact hbound.trans (moving_edge_eq_at p hb control e t p.a hec het hat hea).2.le

/-- The full reverse-moving span has its predecessor commutator in the
starting edge displacement as soon as it is local at the predecessor.
The trapped-radius hypothesis supplies the kernel bounds at its generators. -/
theorem backwardSpan_predecessor_commutator_le_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hlocal : backwardSpan geometry p.a t ≤ stabilizer R p.c) :
    ⁅backwardSpan geometry p.a t, Z R p.c⁆ ≤ edgeDisplacement p.a t := by
  have hEQ : edgeDisplacement p.a t ≤ Z R p.a :=
    (Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)
  have hnorm : Q R p.a ≤ normalizer (edgeDisplacement p.a t : Set (FreeAmalgam R)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.a p.color_a))).trans (centralizer_le hEQ)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hspan : backwardSpan geometry p.a t ≤
      commutatorPreimage (Q R p.a) (Z R p.c) (edgeDisplacement p.a t) := by
    apply iSup_le
    intro e
    apply iSup_le
    intro het
    apply iSup_le
    intro hea
    have hVe := V_le_backwardSpan het hea
    exact le_commutatorPreimage
      (hVe.trans (backwardSpan_le_Q p.color_a hb t))
      (generator_predecessor_commutator_le_edge source p (by omega) control t e hat het hea
        (hVe.trans hlocal))
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)

/-- The exact predecessor comparison required by the second edge choice
in (4.3.7)(i). The favorable Q_d bound supplies locality at c; no product
normality, moving-neighbor symmetry or later escape conclusion is used. -/
theorem predecessorComparison (source : LocalSource L R)
    (control : ∀ p : Counterexample geometry, LocalControl p)
    (rigidity : RigidityFacts geometry) : PredecessorComparison geometry := by
  intro p d t hd hat _hgen hgood
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdist : (cosetGraph R).dist d p.c = 2 :=
    before_dist (geometry := geometry) hd p.before (by decide)
  exact backwardSpan_predecessor_commutator_le_edge source p
    (by have := rigidity.six_lt p; omega) control t hat
    (hgood.trans (Q_le_stabilizer_of_dist_two R d p.c hdc hdist))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
