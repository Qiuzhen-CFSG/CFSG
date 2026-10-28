module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralIntervals

/-!
# The two endpoint noncommutation steps

A mover one vertex beyond the central interval creates a four-edge arc by
folding a track segment about that vertex. The stabilizers of its two end edges
generate the acting group by (2.13). An edge-central involution commuting with
the mover would then be globally central and fix an edge, contradicting the
faithful action. Reversing the track supplies the left-hand statement.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.1), p.396.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.eq_one_of_centralizes_of_fixed_edge (h : CubicTreeAction F)
    {z : G} (hc : ∀ g : G, Commute z g) {a b : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) (ha : z • a = a) (hb : z • b = b) : z = 1 := by
  apply h.action_injective
  ext v
  change z • v = (1 : G) • v
  rw [one_smul]
  have hfix : ∀ w : RankTwo.Vertex F, z • w = w →
      v.type = w.type → z • v = v := by
    intro w hw ht
    obtain ⟨g, rfl⟩ := (RankTwo.same_orbit_iff F w v).2 ht.symm
    rw [← mul_smul, (hc g).eq, mul_smul, hw]
  by_cases ht : v.type = a.type
  · exact hfix a ha ht
  · apply hfix b hb
    have hab' := hab.1
    cases hv : v.type <;> cases ha' : a.type <;> cases hb' : b.type <;> simp_all

theorem CubicTreeAction.not_commute_after_centralRight (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z x : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (hx : x • t.vertex (d.centralRight + 1) = t.vertex (d.centralRight + 1))
    (hxprev : x • t.vertex d.centralRight ≠ t.vertex d.centralRight) :
    ¬ Commute z x := by
  intro hzx
  let b := d.centralRight
  change x • t.vertex (b + 1) = t.vertex (b + 1) at hx
  have hlt := d.central_lt
  have h01 : (RankTwo.graph F).Adj (t.vertex (b - 1)) (t.vertex b) := by
    simpa only [sub_add_cancel] using t.adjacent (b - 1)
  have h12 := t.adjacent b
  have h23 : (RankTwo.graph F).Adj (t.vertex (b + 1)) (x • t.vertex b) := by
    simpa only [hx] using trackGraphAction.map_adj x h12.symm
  have h34 := trackGraphAction.map_adj x h01.symm
  let p : BasedWalk (RankTwo.graph F) 4 (t.vertex (b - 1)) :=
    ⟨⟨t.vertex b, h01⟩, ⟨⟨t.vertex (b + 1), h12⟩,
      ⟨⟨x • t.vertex b, h23⟩, ⟨⟨x • t.vertex (b - 1), h34⟩, PUnit.unit⟩⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, hxprev, ?_, trivial⟩
    · intro he
      have hi := t.injective he
      omega
    · intro he
      have he' : x • t.vertex (b - 1) = x • t.vertex (b + 1) := he.trans hx.symm
      have hi := t.injective ((MulAction.toPerm x).injective he')
      omega
  have hgen := h.arc_stabilizers_generate_separated hshort (by omega : 4 ≤ s) p hp
    (i := 1) (j := 3) (by decide) (by decide)
  let C := centralizer ({z} : Set G)
  have hzedge := d.central (b - 1) (by dsimp [b]; omega) (by dsimp [b]; omega)
  have hCleft : arcIntervalStabilizer p.toWalk 0 1 ≤ C := by
    intro a ha y hy
    have hey : y = z := Set.mem_singleton_iff.mp hy
    subst y
    apply hzedge.2 a
    exact ⟨ha 0 (by decide) (by decide), by
      change a • t.vertex (b - 1 + 1) = t.vertex (b - 1 + 1)
      simpa only [sub_add_cancel] using
        (show a • t.vertex b = t.vertex b from ha 1 (by decide) (by decide))⟩
  have hCright : arcIntervalStabilizer p.toWalk 3 4 ≤ C := by
    intro a ha y hy
    have hey : y = z := Set.mem_singleton_iff.mp hy
    subst y
    have ha3 : a • (x • t.vertex b) = x • t.vertex b := ha 3 (by decide) (by decide)
    have ha4 : a • (x • t.vertex (b - 1)) = x • t.vertex (b - 1) :=
      ha 4 (by decide) (by decide)
    let a' := x⁻¹ * a * x
    have ha' : a' ∈ t.edgeStabilizer (b - 1) := by
      refine ⟨?_, ?_⟩
      · change (x⁻¹ * a * x) • t.vertex (b - 1) = t.vertex (b - 1)
        simp only [mul_smul, ha4, inv_smul_smul]
      · change (x⁻¹ * a * x) • t.vertex (b - 1 + 1) = t.vertex (b - 1 + 1)
        simp only [sub_add_cancel, mul_smul, ha3, inv_smul_smul]
    have hh := (hzedge.2 a' ha').conj x
    have hxz : x * z * x⁻¹ = z := by
      rw [hzx.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [hxz, a', mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
      mul_inv_cancel, mul_one] using hh.eq
  have hCtop : C = ⊤ := top_unique (by rw [← hgen]; exact sup_le hCleft hCright)
  have hzall : ∀ g : G, Commute z g := by
    intro g
    have hg : g ∈ C := by rw [hCtop]; trivial
    exact hg z (Set.mem_singleton z)
  have he : z = 1 := h.eq_one_of_centralizes_of_fixed_edge hzall h01
    hzedge.fixes_left (by simpa only [sub_add_cancel] using hzedge.fixes_right)
  have hzorder := hz.1
  simp only [he, orderOf_one] at hzorder
  omega

theorem CubicTreeAction.not_commute_before_centralLeft (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z x : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (hx : x • t.vertex (d.centralLeft - 1) = t.vertex (d.centralLeft - 1))
    (hxnext : x • t.vertex d.centralLeft ≠ t.vertex d.centralLeft) :
    ¬ Commute z x := by
  apply h.not_commute_after_centralRight hs hshort t.reverse
    (show t.reverse.CentralInvolution z from ⟨hz.1, by
      obtain ⟨i, hi⟩ := hz.2
      refine ⟨-i - 1, (Track.centralEdge_reverse_iff t z _).2 ?_⟩
      have he : -(-i - 1) - 1 = i := by omega
      simpa only [he] using hi⟩) d.reverse
  · have he : -(-d.centralLeft + 1) = d.centralLeft - 1 := by omega
    simpa only [Track.CentralInterval.reverse, Track.reverse, he] using hx
  · simpa only [Track.CentralInterval.reverse, Track.reverse, neg_neg] using hxnext

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
