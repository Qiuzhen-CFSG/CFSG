module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathSingularity
public import Theory.GroupAction.CubicTree.ArcTransport

/-!
# The epsilon-two path regularity bound

A nonregular path of length b−2 bounds the first singular length. Taking the
minimum over all starting vertices retains both vertex orbits. Reversal makes
every shorter path regular at both ends, and the existing prefix induction
proves conjugacy of paths of every length at most the minimum, whenever their
starting vertices have the same type. The source application constructs the
nonregular witness from the critical-center identities.

This supplies s ≤ b−2 and the Chapter 3 path-transitivity fact needed next in
(7.5)(5). The later quotient exclusion and final index argument remain separate.

Source: DGS, *Groups and Graphs* (1985), (3.4), pp.73--74, and (7.5)(4), p.130.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
open SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The minimum singular length is realized, every shorter path is regular
at both ends, and all paths up to that length with the same initial vertex
orbit are conjugate. A bounded singular witness supplies finiteness. -/
theorem graph_first_singular_length (_h : LocallyRankOneTriple P B)
    {n : ℕ} {v : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n v) (hp : p.Nonbacktracking)
    (hbad : ¬ RightRegular (A := G) p) :
    ∃ s : ℕ, 0 < s ∧ s ≤ n ∧
      (∀ k x (q : BasedWalk (graph (family P)) k x),
        k < s → q.Nonbacktracking → Regular (A := G) q) ∧
      (∃ x, ∃ q : BasedWalk (graph (family P)) s x,
        q.Nonbacktracking ∧ ¬ RightRegular (A := G) q) ∧
      (∀ k (_hk : k ≤ s) x y
        (q : BasedWalk (graph (family P)) k x)
        (r : BasedWalk (graph (family P)) k y),
        q.Nonbacktracking → r.Nonbacktracking → x.type = y.type →
        ∃ g : G, q.vertices.map (g • ·) = r.vertices) := by
  classical
  have hex : ∃ k, ∃ x, ∃ q : BasedWalk (graph (family P)) k x,
      q.Nonbacktracking ∧ ¬ RightRegular (A := G) q := ⟨n,v,p,hp,hbad⟩
  let s := Nat.find hex
  have hmin : ∀ k < s, ∀ x (q : BasedWalk (graph (family P)) k x),
      q.Nonbacktracking → RightRegular (A := G) q := by
    intro k hk x q hq
    by_contra hn
    exact Nat.find_min hex hk ⟨x,q,hq,hn⟩
  have hs : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro he
    obtain ⟨x,q,hq,hn⟩ := Nat.find_spec hex
    have hbadzero : ∃ x, ∃ q : BasedWalk (graph (family P)) 0 x,
        q.Nonbacktracking ∧ ¬ RightRegular (A := G) q := by
      rw [←he]
      exact ⟨x,q,hq,hn⟩
    obtain ⟨x,q,_,hn⟩ := hbadzero
    cases q
    exact hn (rightRegular_zero_of_neighbor_transitive
      (fun {x y z} hxy hxz => locally_transitive (family P) hxy hxz) x)
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  refine ⟨s,hs,Nat.find_min' hex ⟨v,p,hp,hbad⟩,?_,Nat.find_spec hex,?_⟩
  · intro k x q hk hq
    exact regular_of_all_rightRegular (hmin k hk) q hq
  · intro k hk x y q r hq hr ht
    exact arcTransitive_of_short_rightRegular hact s (fun k x q hk hq => hmin k hk x q hq) hk q r hq hr
      ((same_orbit_iff (family P) x y).mpr ht)

/-- DGS (7.5)(4) with the minimum and the (3.4)(c) transitivity property
both constructed from the same actual critical graph. -/
theorem graph_epsilonTwo_regularity_length
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
 :
    b (family P) = 2 ∨ ∃ s : ℕ, 0 < s ∧ s + 2 ≤ b (family P) ∧
      (∀ k x (q : BasedWalk (graph (family P)) k x),
        k < s → q.Nonbacktracking → Regular (A := G) q) ∧
      (∃ x, ∃ q : BasedWalk (graph (family P)) s x,
        q.Nonbacktracking ∧ ¬ RightRegular (A := G) q) ∧
      (∀ k (_hk : k ≤ s) x y
        (q : BasedWalk (graph (family P)) k x)
        (r : BasedWalk (graph (family P)) k y),
        q.Nonbacktracking → r.Nonbacktracking → x.type = y.type →
        ∃ g : G, q.vertices.map (g • ·) = r.vertices) := by
  rcases graph_epsilonTwo_nonregular_path h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ with hb | ⟨n,p,hlen,hp,hbad⟩
  · exact Or.inl hb
  obtain ⟨s,hs,hsn,hshort,hbad,htrans⟩ := graph_first_singular_length h p hp hbad
  exact Or.inr ⟨s,hs,by omega,hshort,hbad,htrans⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
