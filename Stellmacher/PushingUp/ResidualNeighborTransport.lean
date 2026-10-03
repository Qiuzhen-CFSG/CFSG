module
public import Stellmacher.PushingUp.CriticalDistanceBasic
public import Stellmacher.TwoResidualSylowSupplement

/-!
# Residual transport of vertices at distance two

At an `M`-orbit vertex of the free-amalgam graph, the 2-residual of the
finite vertex stabilizer acts transitively on its neighbors. Consequently,
if two vertices are each at distance two from that vertex, a residual
element moves the first to distance at most two from the second.

This is the geometric move used in Stellmacher, *Pushing up*, Arch. Math.
46 (1986), proof of (3.3)(6), p. 15. The formulation allows the moved
vertices to coincide, which is sufficient for the subsequent critical
distance argument. Only the local stabilizers are finite; neither the
free amalgam nor its vertex set is assumed finite.

The incident edge is a Sylow 2-subgroup of the vertex stabilizer. The
Sylow supplement theorem factors a transporter as an edge element followed
by a residual element; this order respects the right action. The edge
element fixes the chosen neighbor, so the residual element gives the same
transport. Apply this to the middle vertices of two length-two paths and
use their remaining edges to bound the new distance.
-/

open Stellmacher Stellmacher.PushingUp.AmalgamGraph
namespace Stellmacher.PushingUp
universe u
variable {M : Type u} [Group M]

private theorem residual_transitive_neighbors [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a d e : Vertex S) (ha : InMVertexOrbit S a)
    (had : Adjacent S a d) (hae : Adjacent S a e) :
    ∃ g ∈ (twoResidualAmbient (⊤ : Subgroup (stabilizer S a))).map
      (stabilizer S a).subtype, act S g d = e := by
  classical
  let R := twoResidualAmbient (⊤ : Subgroup (stabilizer S a))
  have hN : (twoResidualSubgroup (⊤ : Subgroup (stabilizer S a))).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N =>
      Subgroup.normal_iInf_normal fun hN => hN.1
  let _ : R.Normal := hN.map _ (fun y => ⟨⟨y, by simp⟩, rfl⟩)
  obtain ⟨P, hP⟩ := incident_edgeStabilizer_isSylow S T hTS a d ha had
  obtain ⟨g, hga, hgde⟩ := stabilizer_transitive_neighbors S a had hae
  have hsup : (P : Subgroup (stabilizer S a)) ⊔ R = ⊤ := by
    rw [sup_comm]
    exact twoResidualAmbient_top_sup_sylow P
  have hg : (⟨g, hga⟩ : stabilizer S a) ∈ (P : Subgroup (stabilizer S a)) ⊔ R := by
    rw [hsup]
    trivial
  obtain ⟨p, hp, r, hr, hpr⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hpd : act S (p : FreeAmalgam S) d = d := by
    have hpmap : (p : FreeAmalgam S) ∈ (P : Subgroup (stabilizer S a)).map
        (stabilizer S a).subtype := ⟨p, hp, rfl⟩
    rw [hP] at hpmap
    exact hpmap.2
  refine ⟨r, ⟨r, hr, rfl⟩, ?_⟩
  have hpr' : (p : FreeAmalgam S) * r = g := congrArg Subtype.val hpr
  rw [← hpr', act_mul, hpd] at hgde
  exact hgde

/-- The local residual can move any two distance-two vertices to within two
steps of one another. -/
public theorem residual_moves_distance_two_vertices_close [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a u c : Vertex S) (ha : InMVertexOrbit S a)
    (hau : (cosetGraph S).dist a u = 2)
    (hac : (cosetGraph S).dist a c = 2) :
    ∃ g ∈ (twoResidualAmbient (⊤ : Subgroup (stabilizer S a))).map
      (stabilizer S a).subtype, (cosetGraph S).dist (act S g u) c ≤ 2 := by
  have common : ∀ y, (cosetGraph S).dist a y = 2 →
      ∃ d, Adjacent S a d ∧ Adjacent S d y := by
    intro y hay
    obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a y
    rw [hay] at hp
    cases p with
    | nil => simp at hp
    | cons had q =>
      cases q with
      | nil => simp at hp
      | cons hdy q =>
        have hq : q.length = 0 := by simpa using hp
        have heq := SimpleGraph.Walk.length_eq_zero_iff.mp hq
        cases heq
        exact ⟨_, (cosetGraph_adj S _ _).1 had, (cosetGraph_adj S _ _).1 hdy⟩
  obtain ⟨d, had, hdu⟩ := common u hau
  obtain ⟨e, hae, hec⟩ := common c hac
  obtain ⟨g, hg, hgde⟩ := residual_transitive_neighbors S T hTS a d e ha had hae
  refine ⟨g, hg, ?_⟩
  have hue : Adjacent S (act S g u) e := by
    rw [← hgde]
    exact (adjacent_act_iff S g u d).2 (adjacent_symm S hdu)
  exact SimpleGraph.dist_le
    (SimpleGraph.Walk.cons ((cosetGraph_adj S _ _).2 hue)
      (SimpleGraph.Walk.cons ((cosetGraph_adj S _ _).2 hec) SimpleGraph.Walk.nil))
end Stellmacher.PushingUp
