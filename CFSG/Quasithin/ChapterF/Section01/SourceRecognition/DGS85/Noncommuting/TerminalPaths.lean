module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LinearPathAction

/-!
# Singular suffixes and their actual path stabilizers

Short-path regularity places the first singular path at the end of any
sufficiently long path of the same endpoint type. The Chapter 6 complement
theorem supplies its edge supplement, so a linear terminal quotient and an
escaping two-group in the path stabilizer contradict singularity. Distance
bounds place the critical center and the radius-two actor in the required
literal path stabilizers.

Source: DGS, *Groups and Graphs* (1985), (3.4), (6.7), and (7.5)(5),
printed pp.129--130.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
open SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A first singular path can be placed at the end of any sufficiently long
nonbacktracking path whose endpoint has the same type. The literal last
edge and all path vertices are retained. -/
theorem graph_singular_terminal_subpath
    {s n : ℕ} (hsn : s + 1 ≤ n + 1)
    (hshort : ∀ k x (q : BasedWalk (graph (family P)) k x),
      k < s+1 → q.Nonbacktracking → Regular (A := G) q)
    {v x : Vertex (family P)}
    (p : BasedWalk (graph (family P)) (n+1) v)
    (q : BasedWalk (graph (family P)) (s+1) x)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (hbad : ¬ RightRegular (A := G) q) (ht : p.endpoint.type = q.endpoint.type) :
    ∃ y, ∃ r : BasedWalk (graph (family P)) (s+1) y,
      r.Nonbacktracking ∧ ¬ RightRegular (A := G) r ∧
      r.endpoint = p.endpoint ∧ r.penultimate = p.penultimate ∧
      ∀ z ∈ r.vertices, z ∈ p.vertices := by
  let a := (reverse p).take (s+1) hsn
  have ha : a.Nonbacktracking := nonbacktracking_take hsn _ (nonbacktracking_reverse p hp)
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  obtain ⟨g,hg⟩ := arcTransitive_of_short_rightRegular hact (s+1)
    (fun k x q hk hq => (hshort k x q hk hq).2) le_rfl a (reverse q) ha
    (nonbacktracking_reverse q hq) ((same_orbit_iff (family P) _ _).mpr ht)
  refine ⟨a.endpoint,reverse a,nonbacktracking_reverse a ha,?_,endpoint_reverse a,?_,?_⟩
  · intro hr
    apply hbad
    apply (leftRegular_reverse_iff q).mp
    exact leftRegular_of_conjugate hact a (reverse q) g hg ((rightRegular_reverse_iff a).mp hr)
  · rw [penultimate_reverse]
    change ((reverse p).1 : Vertex (family P)) = p.penultimate
    exact first_reverse p
  · intro z hz
    rw [vertices_reverse,List.mem_reverse,BasedWalk.vertices_take] at hz
    rw [vertices_reverse] at hz
    exact List.mem_reverse.mp (List.mem_of_mem_take hz)

/-- A linear marked terminal vertex cannot have a first singular suffix
whose fixer contains an escaping two-subgroup. The path supplement is
derived from short-path regularity by the proved Chapter 6 theorem. -/
theorem graph_linear_terminal_nonsingular
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {s n : ℕ} (hsn : s + 1 ≤ n + 1)
    (hshort : ∀ k x (q : BasedWalk (graph (family P)) k x),
      k < s+1 → q.Nonbacktracking → Regular (A := G) q)
    {v x : Vertex (family P)}
    (p : BasedWalk (graph (family P)) (n+1) v)
    (q : BasedWalk (graph (family P)) (s+1) x)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (ht : p.endpoint.type = q.endpoint.type)
    (c : LocalRankOneData (stabilizer (family P) p.endpoint)
      (stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.penultimate))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) p.endpoint))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q (family P) p.endpoint).subgroupOf c.Pstar)
    (A : Subgroup G) (hpA : IsPGroup 2 A)
    (hAp : A ≤ pathStabilizer (family P) p) (hAQ : ¬ A ≤ Q (family P) p.endpoint) :
    RightRegular (A := G) q := by
  by_contra hbad
  obtain ⟨y,r,hr,hbad,he,hp',hsub⟩ := graph_singular_terminal_subpath hsn hshort p q hp hq hbad ht
  have hAr : A ≤ pathStabilizer (family P) r := fun _ ha z hz => hAp ha z (hsub z hz)
  have hem : r.endpoint ∈ r.vertices := by
    simpa only [BasedWalk.support_toWalk] using r.toWalk.end_mem_support
  have hpm : r.penultimate ∈ r.vertices := by
    have hh := (r.take s (Nat.le_succ s)).toWalk.end_mem_support
    rw [BasedWalk.support_toWalk,BasedWalk.endpoint_take_penultimate,BasedWalk.vertices_take] at hh
    exact List.mem_of_mem_take hh
  obtain ⟨K,hKr,_,hKE,_⟩ := graph_path_complement_of_short_regular h hB hbranch
    le_rfl hshort r hr r.adj_penultimate_endpoint.symm hem hpm
  have hgen : pathStabilizer (family P) r ⊔
      (stabilizer (family P) r.endpoint ⊓ stabilizer (family P) r.penultimate).pCoreIn 2 =
      stabilizer (family P) r.endpoint ⊓ stabilizer (family P) r.penultimate := by
    apply le_antisymm (sup_le (pathStabilizer_le_edge (family P) r hem hpm) (pCoreIn_le _ _))
    exact hKE.symm.le.trans (sup_le_sup_right hKr _)
  let c' : LocalRankOneData (stabilizer (family P) r.endpoint)
      (stabilizer (family P) r.endpoint ⊓ stabilizer (family P) r.penultimate) := {
    finite_P := by simpa only [he] using c.finite_P
    Pstar := c.Pstar
    Pstar_le := by simpa only [he] using c.Pstar_le
    normal := (congrArg (fun z => (c.Pstar.subgroupOf (stabilizer (family P) z)).Normal) he).mpr c.normal
    same_core := by simpa only [he] using c.same_core
    supplement := by simpa only [he,hp'] using c.supplement
    characteristic_two := (congrArg (fun z => Theory.GroupTheory.generalizedFitting (stabilizer (family P) z) = pCore 2 (stabilizer (family P) z)) he).mpr c.characteristic_two
    sylow := c.sylow
    borel_eq := by simpa only [he,hp'] using c.borel_eq
    quotient := c.quotient }
  exact hbad (graph_linear_path_rightRegular h hB r c' (by simpa only [he] using ho) π hπ
    (by simpa only [he] using hk) hgen A hpA hAr (by rw [he]; exact hAQ))

private theorem path_vertex_distance_le {n : ℕ} {v z : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n v) (hz : z ∈ p.vertices) :
    (graph (family P)).dist v z ≤ n := by
  classical
  have hm : z ∈ p.toWalk.support := by rwa [BasedWalk.support_toWalk]
  have hh := (graph (family P)).dist_le (p.toWalk.takeUntil z hm)
  have hl := p.toWalk.length_takeUntil_le_length hm
  rw [BasedWalk.length_toWalk] at hl
  exact hh.trans hl

/-- The original critical center fixes every vertex of a path whose length
is at most the global critical distance. -/
theorem graph_center_le_pathStabilizer (h : LocallyRankOneTriple P B)
    {n : ℕ} {v : Vertex (family P)} (p : BasedWalk (graph (family P)) n v)
    (hn : n ≤ b (family P)) : Z (family P) v ≤ pathStabilizer (family P) p := by
  let := finite_endpoints h
  intro a ha z hz
  exact Z_le_stabilizer_of_dist_le_b (family P) h.generate v z
    ((path_vertex_distance_le p hz).trans hn) ha

/-- The radius-two actor fixes the path to the penultimate even vertex
by the distance budget, and also the final odd vertex by its proved core
containment. This keeps the full permutation kernel distinct from O₂. -/
theorem graph_radius_two_le_extended_pathStabilizer (h : LocallyRankOneTriple P B)
    {n : ℕ} {v t : Vertex (family P)} (p : BasedWalk (graph (family P)) n v)
    (ht : (graph (family P)).Adj p.endpoint t) (hn : n+2 ≤ b (family P))
    (hcore : V (family P) v 2 ≤ Q (family P) p.endpoint) :
    V (family P) v 2 ≤ pathStabilizer (family P) (p.snoc ht) := by
  have hfix : V (family P) v 2 ≤ stabilizer (family P) t :=
    (hcore.trans (source_Z_Q_U h p.endpoint).2).trans
      ((ballKernel_one_le_edge (family P) ht).trans inf_le_right)
  intro a ha z hz
  rw [BasedWalk.vertices_snoc,List.mem_append,List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact graph_V_le_stabilizer_of_distance h
      (by have hh := path_vertex_distance_le p hz; omega) ha
  · exact hfix ha

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
