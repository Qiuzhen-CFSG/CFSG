module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralComparison

/-!
# Balanced margins and the unique central block

Translating a second involution into the boundary alignment of (6.2) compares
its left margin with the first involution's right margin. Both differ by at
most one. A second central edge outside the chosen block would be fixed by a
suitable translate of the original involution, contradicting the established
noncommutation. This proves uniqueness of the central block directly, without
assuming that a different edge belongs to a block of the same maximal length.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.3), p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.central_margin_comparison (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z') :
    d'.leftMargin ≤ d.rightMargin + 1 ∧ d.rightMargin ≤ d'.leftMargin + 1 := by
  let k : ℤ := (d.centralRight - d'.fixedLeft + 1) / 2
  let e := d'.shift k
  have hnear : d.centralRight ≤ e.fixedLeft ∧ e.fixedLeft ≤ d.centralRight + 1 := by
    dsimp only [e, Track.CentralInterval.shift, k]
    omega
  have hother := h.left_boundary_of_right_boundary hs hshort t hz (hz'.shift k) d e hnear
  have hd := d.rightMargin_cast
  have he := d'.leftMargin_cast
  dsimp only [e, Track.CentralInterval.shift] at hnear hother
  omega

private theorem CubicTreeAction.centralEdge_index_lt_right (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) {i : ℤ} (hi : t.CentralEdge z i) : i < d.centralRight := by
  by_contra hge
  have hnot := d.not_central_right
  have hne : i ≠ d.centralRight := fun he => hnot (he ▸ hi)
  have hpos : d.centralRight + 1 ≤ i := by omega
  have hfixR := (d.fixed_iff (i + 1)).1 hi.fixes_right
  let k : ℤ := (d.centralRight - d.fixedLeft + 1) / 2
  have hdL := d.centralLeft_mem
  have hdLt := d.central_lt
  have hk : 0 < k := by dsimp only [k]; omega
  let e := d.shift k
  have hnear : d.centralRight ≤ e.fixedLeft ∧ e.fixedLeft ≤ d.centralRight + 1 := by
    dsimp only [e, Track.CentralInterval.shift, k]
    omega
  have hnc := h.not_commute_of_right_boundary hs hshort t hz d e hnear
  apply hnc
  apply hi.2
  refine ⟨(e.fixed_iff i).2 ⟨?_, ?_⟩, (e.fixed_iff (i + 1)).2 ⟨?_, ?_⟩⟩
  · omega
  · change i ≤ d.fixedRight + 2 * k
    omega
  · omega
  · change i + 1 ≤ d.fixedRight + 2 * k
    omega

/-- Every edge on which the involution is central belongs to its chosen
central block; the block is therefore unique. -/
theorem CubicTreeAction.centralEdge_iff_in_centralInterval (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (i : ℤ) :
    t.CentralEdge z i ↔ d.centralLeft ≤ i ∧ i < d.centralRight := by
  constructor
  · intro hi
    have hright := h.centralEdge_index_lt_right hs hshort t hz d hi
    have hrev : t.reverse.CentralInvolution z := by
      refine ⟨hz.1, ?_⟩
      obtain ⟨j, hj⟩ := hz.2
      refine ⟨-j - 1, (Track.centralEdge_reverse_iff t z _).2 ?_⟩
      have he : -(-j - 1) - 1 = j := by omega
      simpa only [he] using hj
    have hi' : t.reverse.CentralEdge z (-i - 1) := by
      apply (Track.centralEdge_reverse_iff t z _).2
      have he : -(-i - 1) - 1 = i := by omega
      simpa only [he] using hi
    have hleft := h.centralEdge_index_lt_right hs hshort t.reverse hrev d.reverse hi'
    change -i - 1 < -d.centralLeft at hleft
    exact ⟨by omega, hright⟩
  · exact fun hi => d.central i hi.1 hi.2

/-- A central block has at most two edges. Three consecutive central edges
would centralize the two end-edge stabilizers of a short arc, hence all of the
faithful acting group. -/
theorem CubicTreeAction.centralInterval_length_le_two (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) : d.centralRight - d.centralLeft ≤ 2 := by
  by_contra hn
  let a := d.centralLeft
  have h01 := t.adjacent a
  have h12 : (RankTwo.graph F).Adj (t.vertex (a + 1)) (t.vertex (a + 2)) := by
    simpa only [show a + 1 + 1 = a + 2 by omega] using t.adjacent (a + 1)
  have h23 : (RankTwo.graph F).Adj (t.vertex (a + 2)) (t.vertex (a + 3)) := by
    simpa only [show a + 2 + 1 = a + 3 by omega] using t.adjacent (a + 2)
  let p : BasedWalk (RankTwo.graph F) 3 (t.vertex a) :=
    ⟨⟨t.vertex (a + 1), h01⟩, ⟨⟨t.vertex (a + 2), h12⟩,
      ⟨⟨t.vertex (a + 3), h23⟩, PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, ?_, trivial⟩
    · intro he
      have hi := t.injective he
      omega
    · intro he
      have hi := t.injective he
      omega
  have hgen := h.arc_stabilizers_generate_separated hshort (by omega : 3 ≤ s) p hp
    (i := 1) (j := 2) (by decide) (by decide)
  let C := centralizer ({z} : Set G)
  have he0 := d.central a (by rfl) (by dsimp [a]; omega)
  have he2 := d.central (a + 2) (by dsimp [a]; omega) (by dsimp [a]; omega)
  have hCleft : arcIntervalStabilizer p.toWalk 0 1 ≤ C := by
    intro g hg y hy
    have hey : y = z := Set.mem_singleton_iff.mp hy
    subst y
    apply he0.2 g
    exact ⟨hg 0 (by decide) (by decide), hg 1 (by decide) (by decide)⟩
  have hCright : arcIntervalStabilizer p.toWalk 2 3 ≤ C := by
    intro g hg y hy
    have hey : y = z := Set.mem_singleton_iff.mp hy
    subst y
    apply he2.2 g
    refine ⟨hg 2 (by decide) (by decide), ?_⟩
    change g • t.vertex (a + 2 + 1) = t.vertex (a + 2 + 1)
    simpa only [show a + 2 + 1 = a + 3 by omega] using
      (show g • t.vertex (a + 3) = t.vertex (a + 3) from hg 3 (by decide) (by decide))
  have hCtop : C = ⊤ := top_unique (by rw [← hgen]; exact sup_le hCleft hCright)
  have hzall : ∀ g : G, Commute z g := by
    intro g
    have hg : g ∈ C := by rw [hCtop]; trivial
    exact hg z (Set.mem_singleton z)
  have he : z = 1 := h.eq_one_of_centralizes_of_fixed_edge hzall h01
    he0.fixes_left he0.fixes_right
  have hzorder := hz.1
  simp only [he, orderOf_one] at hzorder
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
