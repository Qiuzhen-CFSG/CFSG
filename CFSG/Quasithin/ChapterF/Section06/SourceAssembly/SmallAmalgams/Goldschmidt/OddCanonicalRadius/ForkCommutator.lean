module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts
public import Theory.GroupAction.CubicTree.TrackArcs
public import Theory.GroupAction.ThreePointKernelSeparation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The far commutation in Goldschmidt (6.11.1)

A four-arc stabilizer moves a fork to the next track vertex. Its initial
vertex is the center of the far label, so it commutes with that label.
The far label fixes the star at the transported endpoint, hence fixes the
original fork endpoint. Equivariance of the canonical labels translates
this fixed point into the required commutation of the first commutator.

Source: Goldschmidt (1980), (6.11.1), printed pp.401--402.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem fork_fixed_of_four_arc
    (t : Track (RankTwo.graph F) G) (a : ℤ)
    (hregular : RightRegular (A := G) (t.arc (a-2) 4))
    (q z : G)
    (hcentral : ∀ g ∈ RankTwo.stabilizer F (t.vertex (a-2)), Commute q g)
    (hstar : ∀ w, (RankTwo.graph F).Adj (t.vertex (a+3)) w → q • w = w)
    (hzfix : z • t.vertex (a+2) = t.vertex (a+2))
    (hzmove : z • t.vertex (a+1) ≠ t.vertex (a+1)) :
    q • (z • t.vertex a) = z • t.vertex a := by
  have h12 : (RankTwo.graph F).Adj (t.vertex (a+1)) (t.vertex (a+2)) := by
    simpa only [show a+1+1=a+2 by omega] using t.adjacent (a+1)
  have hzforward : Forward (t.arc (a-2) 4) (z • t.vertex (a+1)) := by
    rw [Forward, t.arc_endpoint, t.arc_penultimate]
    have hadj := trackGraphAction.map_adj z h12.symm
    simpa only [hzfix, show a-2+(4:ℕ)=a+2 by omega,
      show a-2+(3:ℕ)=a+1 by omega] using And.intro hadj hzmove
  have hforward : Forward (t.arc (a-2) 4) (t.vertex (a+3)) := by
    simpa only [show a-2+(4:ℕ)+1=a+3 by omega] using t.arc_forward (a-2) 4
  obtain ⟨g, hg, hmove⟩ := hregular _ _ hzforward hforward
  have hg0 : g • t.vertex (a-2) = t.vertex (a-2) :=
    t.mem_segmentFixer.mp ((t.fixes_arc_iff (a-2) 4 g).1 hg) _ le_rfl (by omega)
  have hcomm : Commute q g := hcentral g hg0
  have hadj : (RankTwo.graph F).Adj (t.vertex (a+3)) (g • (z • t.vertex a)) := by
    have hh := trackGraphAction.map_adj g (trackGraphAction.map_adj z (t.adjacent a).symm)
    rwa [hmove] at hh
  have hfixed := hstar _ hadj
  apply (MulAction.toPerm g).injective
  calc
    g • (q • (z • t.vertex a)) = q • (g • (z • t.vertex a)) := by
      rw [← mul_smul, hcomm.symm.eq, mul_smul]
    _ = g • (z • t.vertex a) := hfixed

private theorem star_fixed_of_track_triple (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (q : G)
    (hprev : q • t.vertex (a-1) = t.vertex (a-1))
    (hcenter : q • t.vertex a = t.vertex a)
    (hnext : q • t.vertex (a+1) = t.vertex (a+1)) :
    ∀ w, (RankTwo.graph F).Adj (t.vertex a) w → q • w = w := by
  apply MulAction.fixes_three_point_set _ (h.card_neighbor _) q
    (fun w => by
      change (RankTwo.graph F).Adj (t.vertex a) w ↔
        (RankTwo.graph F).Adj (t.vertex a) (q • w)
      simpa only [hcenter] using (trackGraphAction.adj_iff q
        (x := t.vertex a) (y := w)).symm)
    (x := t.vertex (a-1)) (y := t.vertex (a+1))
  · change (RankTwo.graph F).Adj (t.vertex a) (t.vertex (a-1))
    simpa only [sub_add_cancel] using (t.adjacent (a-1)).symm
  · exact t.adjacent a
  · intro he
    have := t.injective he
    omega
  · exact hprev
  · exact hnext

/-- The one far translated commutation needed by the source odd-radius
argument, with every local fork premise supplied by the actual labels. -/
theorem CanonicalLabelSetup.far_commutator_commutes (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hr : 5 ≤ d.radius) (hodd : Odd d.radius) :
    Commute ⁅d.label (d.track.vertex d.center),
        d.label (d.track.vertex (d.center + (d.radius : ℤ) + 3))⁆
      (d.label (d.track.vertex (d.center + (d.radius : ℤ) + 5))) := by
  let t := d.track
  let c := d.center
  let r : ℤ := d.radius
  let z := d.label (t.vertex c)
  let x := d.label (t.vertex (c+r+3))
  let y := d.label (t.vertex (c+r+5))
  change Commute ⁅z,x⁆ y
  obtain ⟨k, hk⟩ := hodd
  have hkZ : r = 2*(k : ℤ)+1 := by dsimp [r]; omega
  have hxcoord : c+r+3 = c+2*((k : ℤ)+2) := by omega
  have hycoord : c+r+5 = c+2*((k : ℤ)+3) := by omega
  have hxtype : (t.vertex (c+r+3)).type = d.side := by
    rw [hxcoord]
    exact d.shifted_type ((k : ℤ)+2)
  have hytype : (t.vertex (c+r+5)).type = d.side := by
    rw [hycoord]
    exact d.shifted_type ((k : ℤ)+3)
  have hyfixed (i : ℤ) : y • t.vertex i = t.vertex i ↔
      c+r+5-(r+1) ≤ i ∧ i ≤ c+r+5+(r+1) := by
    have hh := d.shifted_fixed_iff ((k : ℤ)+3) i
    change d.label (t.vertex (c+2*((k : ℤ)+3))) • t.vertex i = t.vertex i ↔
      c+2*((k : ℤ)+3)-(r+1) ≤ i ∧ i ≤ c+2*((k : ℤ)+3)+(r+1) at hh
    rwa [← hycoord] at hh
  have hzfixed (i : ℤ) : z • t.vertex i = t.vertex i ↔ c-(r+1) ≤ i ∧ i ≤ c+(r+1) := by
    have hh := d.shifted_fixed_iff 0 i
    simpa only [mul_zero, add_zero] using hh
  have hyx : y • t.vertex (c+r+3) = t.vertex (c+r+3) :=
    (hyfixed _).2 (by dsimp [r]; omega)
  have hxy : Commute x y := (d.central _ hxtype).2 y hyx
  have hystar : ∀ w, (RankTwo.graph F).Adj (t.vertex (c+r)) w → y • w = w :=
    star_fixed_of_track_triple h t (c+r) y
      ((hyfixed _).2 (by dsimp [r]; omega))
      ((hyfixed _).2 (by dsimp [r]; omega))
      ((hyfixed _).2 (by dsimp [r]; omega))
  let a := -(c+r+3)
  have hcentral : ∀ g ∈ RankTwo.stabilizer F (t.reverse.vertex (a-2)), Commute y g := by
    have he : t.reverse.vertex (a-2) = t.vertex (c+r+5) := by
      change t.vertex (-(a-2)) = _
      congr 1
      dsimp [a]
      omega
    rw [he]
    exact (d.central _ hytype).2
  have hstar : ∀ w, (RankTwo.graph F).Adj (t.reverse.vertex (a+3)) w → y • w = w := by
    have he : t.reverse.vertex (a+3) = t.vertex (c+r) := by
      change t.vertex (-(a+3)) = _
      congr 1
      dsimp [a]
      omega
    rw [he]
    exact hystar
  have hzfix : z • t.reverse.vertex (a+2) = t.reverse.vertex (a+2) := by
    change z • t.vertex (-(a+2)) = t.vertex (-(a+2))
    apply (hzfixed _).2
    dsimp [a]
    omega
  have hzmove : z • t.reverse.vertex (a+1) ≠ t.reverse.vertex (a+1) := by
    change z • t.vertex (-(a+1)) ≠ t.vertex (-(a+1))
    intro he
    have hh := (hzfixed _).1 he
    dsimp [a] at hh
    omega
  have hfork := fork_fixed_of_four_arc t.reverse a
    (hshort 4 _ _ (by omega) (t.reverse.arc_nonbacktracking (a-2) 4))
    y z hcentral hstar hzfix hzmove
  have hfork' : y • (z • t.vertex (c+r+3)) = z • t.vertex (c+r+3) := by
    change y • (z • t.vertex (-a)) = z • t.vertex (-a) at hfork
    simpa only [a, neg_neg] using hfork
  have hconj : Commute (z*x*z⁻¹) y := by
    have htx : (z • t.vertex (c+r+3)).type = d.side := hxtype
    have hh := (d.central _ htx).2 y hfork'
    rwa [d.conjugate z _ hxtype] at hh
  change Commute ((z*x*z⁻¹)*x⁻¹) y
  exact hconj.mul_left hxy.inv_left

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

