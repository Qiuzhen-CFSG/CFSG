module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralNoncommutation
public import Theory.GroupAction.CubicTree.CentralTranslation

/-!
# Comparing the endpoints of two central involutions

An involution first fixing the track at either of the two vertices next to the
right end of a central interval does not commute with its owner. Translating
one interval by an even amount rules out a larger gap at the other ends: it
would force the same two involutions both to commute and not to commute.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.2), p.396.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.not_commute_of_right_boundary (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (hpos : d.centralRight ≤ d'.fixedLeft ∧ d'.fixedLeft ≤ d.centralRight + 1) :
    ¬ Commute z z' := by
  have hfix := (d'.fixed_iff d'.fixedLeft).2 ⟨le_rfl,
    le_trans d'.centralLeft_mem.1 d'.centralLeft_mem.2⟩
  have hmove : z' • t.vertex (d'.fixedLeft - 1) ≠ t.vertex (d'.fixedLeft - 1) := by
    intro he
    have hh := (d'.fixed_iff _).1 he
    omega
  have he : d'.fixedLeft = d.centralRight ∨ d'.fixedLeft = d.centralRight + 1 := by omega
  rcases he with he | he
  · apply h.not_commute_centralRight t d
    · simpa only [he] using hfix
    · simpa only [he] using hmove
  · apply h.not_commute_after_centralRight hs hshort t hz d
    · simpa only [he] using hfix
    · simpa only [he, add_sub_cancel_right] using hmove

theorem CubicTreeAction.not_commute_of_left_boundary (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G} (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (hpos : d'.centralLeft - 1 ≤ d.fixedRight ∧ d.fixedRight ≤ d'.centralLeft) :
    ¬ Commute z z' := by
  have hfix := (d.fixed_iff d.fixedRight).2 ⟨le_trans d.centralLeft_mem.1 d.centralLeft_mem.2, le_rfl⟩
  have hmove : z • t.vertex (d.fixedRight + 1) ≠ t.vertex (d.fixedRight + 1) := by
    intro he
    have hh := (d.fixed_iff _).1 he
    omega
  have he : d.fixedRight = d'.centralLeft ∨ d.fixedRight = d'.centralLeft - 1 := by omega
  intro hc
  rcases he with he | he
  · exact h.not_commute_centralLeft t d'
      (by simpa only [he] using hfix) (by simpa only [he] using hmove) hc.symm
  · exact h.not_commute_before_centralLeft hs hshort t hz' d'
      (by simpa only [he] using hfix)
      (by simpa only [he, sub_add_cancel] using hmove) hc.symm

theorem CubicTreeAction.left_boundary_of_right_boundary (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (hpos : d.centralRight ≤ d'.fixedLeft ∧ d'.fixedLeft ≤ d.centralRight + 1) :
    d'.centralLeft - 1 ≤ d.fixedRight ∧ d.fixedRight ≤ d'.centralLeft := by
  have hnc := h.not_commute_of_right_boundary hs hshort t hz d d' hpos
  have hdL := d.centralLeft_mem
  have hdR := d.centralRight_mem
  have hdLt := d.central_lt
  have heL := d'.centralLeft_mem
  have heR := d'.centralRight_mem
  have heLt := d'.central_lt
  have hupp : d.fixedRight ≤ d'.centralLeft := by
    by_contra hn
    have hedge := d'.central d'.centralLeft le_rfl heLt
    have hzedge : z ∈ t.edgeStabilizer d'.centralLeft :=
      ⟨(d.fixed_iff _).2 ⟨by omega, by omega⟩,
        (d.fixed_iff _).2 ⟨by omega, by omega⟩⟩
    exact hnc (hedge.2 z hzedge).symm
  refine ⟨?_, hupp⟩
  by_contra hlow
  let k : ℤ := (d'.centralLeft - d.fixedRight) / 2
  have hk : 0 < k := by dsimp [k]; omega
  have hnear : d'.centralLeft - 1 ≤ d.fixedRight + 2 * k ∧
      d.fixedRight + 2 * k ≤ d'.centralLeft := by dsimp [k]; omega
  let e := d.shift k
  have hncs := h.not_commute_of_left_boundary hs hshort t hz' e d' hnear
  have hedge := e.central (e.centralRight - 1) (by
    have hh := e.central_lt; omega) (by omega)
  have hz'edge : z' ∈ t.edgeStabilizer (e.centralRight - 1) := by
    refine ⟨(d'.fixed_iff _).2 ⟨?_, ?_⟩, (d'.fixed_iff _).2 ⟨?_, ?_⟩⟩ <;>
      dsimp only [e, Track.CentralInterval.shift] <;> omega
  exact hncs (hedge.2 z' hz'edge)

/-- The two boundary alignments in source (6.2) are equivalent, and imply
noncommutation of the actual two involutions. -/
theorem CubicTreeAction.central_boundaries_iff (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z') :
    (d.centralRight ≤ d'.fixedLeft ∧ d'.fixedLeft ≤ d.centralRight + 1) ↔
      (d'.centralLeft - 1 ≤ d.fixedRight ∧ d.fixedRight ≤ d'.centralLeft) := by
  constructor
  · exact h.left_boundary_of_right_boundary hs hshort t hz hz' d d'
  · intro hpos
    have hrev (w : G) (hw : t.CentralInvolution w) : t.reverse.CentralInvolution w := by
      refine ⟨hw.1, ?_⟩
      obtain ⟨i, hi⟩ := hw.2
      refine ⟨-i - 1, (Track.centralEdge_reverse_iff t w _).2 ?_⟩
      have he : -(-i - 1) - 1 = i := by omega
      simpa only [he] using hi
    have hh := h.left_boundary_of_right_boundary hs hshort t.reverse
      (hrev z' hz') (hrev z hz) d'.reverse d.reverse (by
        change -d'.centralLeft ≤ -d.fixedRight ∧ -d.fixedRight ≤ -d'.centralLeft + 1
        omega)
    change -d.centralRight - 1 ≤ -d'.fixedLeft ∧ -d'.fixedLeft ≤ -d.centralRight at hh
    omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
