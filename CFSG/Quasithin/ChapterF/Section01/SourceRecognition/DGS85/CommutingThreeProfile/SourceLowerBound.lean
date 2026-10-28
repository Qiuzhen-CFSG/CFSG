module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
public import Theory.GroupAction.CubicTree.ArcTransport

/-!
# The source minimum is longer than six

The source minimum is defined using right regularity, while the two six-path
constructions naturally give one left-regular endpoint.  Reversing an even
arc preserves its endpoint type and exchanges left and right regularity.  Thus
one regular six-path in each vertex orbit contradicts source minimality at
length six.  This is the minimality step used in DGS (12.8).
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open Subgroup.CosetGeometry.RankTwo SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A left-regular nonbacktracking walk of length `N` in each vertex orbit
forces the source minimum to be strictly longer than `N`. -/
theorem sourceS_gt_of_left_regular_orbits
    (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i),
      (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (N : ℕ)
    (hpaths : ∀ i : Bool, ∃ a : Vertex (family P), a.type = i ∧
      ∃ p : BasedWalk (graph (family P)) N a,
        p.Nonbacktracking ∧ LeftRegular (A := G) p) :
    N < sourceS (P := P) := by
  obtain ⟨n,hs,hshort,_,i,p,hp,hbad,_⟩ := source_first_nonregular_parameter h hS
  have he := (sourceS_spec h hS).2.unique hs
  rw [he]
  by_contra hle
  have hlen : n+1 ≤ N := by omega
  obtain ⟨a,ha,q,hq,hleft⟩ := hpaths p.endpoint.type
  let r := q.take (n+1) hlen
  have hr : r.Nonbacktracking := nonbacktracking_take hlen q hq
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ hedge =>
      (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj hedge⟩
  obtain ⟨g,hg⟩ := arcTransitive_of_short_rightRegular hact (n+1)
    (fun k x t hk ht => (hshort k hk x t ht).2) le_rfl r (reverse p)
    hr (nonbacktracking_reverse p hp) ((same_orbit_iff (family P) _ _).mpr ha)
  apply hbad
  apply (leftRegular_reverse_iff p).mp
  exact leftRegular_of_conjugate hact r (reverse p) g hg
    (leftRegular_take q (by omega) hlen hleft)

/-- On an even walk the endpoints have the same type, so either endpoint
regularity orientation supplies the left-regular witnesses needed above. -/
theorem sourceS_gt_of_even_endpoint_regular_orbits
    (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i),
      (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {N : ℕ} (hN : Even N)
    (hpaths : ∀ i : Bool, ∃ a : Vertex (family P), a.type = i ∧
      ∃ p : BasedWalk (graph (family P)) N a,
        p.Nonbacktracking ∧ (LeftRegular (A := G) p ∨ RightRegular (A := G) p)) :
    N < sourceS (P := P) := by
  apply sourceS_gt_of_left_regular_orbits h hS N
  intro i
  obtain ⟨a,ha,p,hp,hreg⟩ := hpaths i
  rcases hreg with hl | hr
  · exact ⟨a,ha,p,hp,hl⟩
  · have he : a.type = p.endpoint.type :=
      (even_walk_iff (family P) p.toWalk).mp (by simpa only [length_toWalk] using hN)
    exact ⟨p.endpoint,he.symm.trans ha,reverse p,nonbacktracking_reverse p hp,
      (leftRegular_reverse_iff p).mpr hr⟩

namespace CommutingThreeProfile.ReducedLayer
open Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two six-path orientations force the literal reduced source parameter
to satisfy `7 ≤ sourceS`. -/
theorem sourceS_seven_le_of_two_six_paths
    (h : HypothesisF11 L S) (i : Bool)
    {a b : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 6 a)
    (q : BasedWalk (graph (reducedFamily L S)) 6 b)
    (ha : a.type = i) (hb : b.type = !i)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (hrp : Regular (A := G₀ L S) p)
    (hrq : LeftRegular (A := G₀ L S) q ∨ RightRegular (A := G₀ L S) q) :
    7 ≤ sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) := by
  have hlt := sourceS_gt_of_even_endpoint_regular_orbits
    (reduced_triple h) (reduced_vertex_sylow h) (N := 6) (by decide) (by
      intro j
      by_cases hij : i = j
      · exact ⟨a,ha.trans hij,p,hp,Or.inl hrp.1⟩
      · have hij' : (!i) = j := by
          cases i <;> cases j <;> simp_all
        exact ⟨b,hb.trans hij',q,hq,hrq⟩)
  exact hlt

end CommutingThreeProfile.ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85
