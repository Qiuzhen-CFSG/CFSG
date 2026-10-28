module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts
public import Theory.GroupAction.RankTwoCosetGeometry.Distance
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Canonical radius-two label relations

The labels at distance at most two commute. At distance four their
commutator is the midpoint label: the opposite endpoint fixes two
vertices in the initial two-edge segment and exchanges the remaining
neighbor, so the three-label product relation determines the commutator.
The three labels around any vertex of the other type generate a Klein
four group. These are the literal relations used to construct the two
finite local groups in Goldschmidt (6.9), pp.400–401.
-/

@[expose] public section
open Subgroup SimpleGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem CanonicalLabelSetup.radiusTwo_commute_of_dist_le_three
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    {a b : RankTwo.Vertex F} (ha : a.type = c.side) (hb : b.type = c.side)
    (hd : (RankTwo.graph F).dist a b ≤ 3) : Commute (c.label a) (c.label b) := by
  exact c.labels_commute_of_dist_le ha hb (hr ▸ hd) (hd.trans hs)

/-- The distance-four commutator follows directly from the three labels
around the second vertex of the arc. The opposite endpoint fixes the midpoint
and exchanges the other two neighbors there. -/
theorem CanonicalLabelSetup.radiusTwo_commutator_of_local_arc
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    {a v m b : RankTwo.Vertex F}
    (ha : a.type = c.side) (_hm : m.type = c.side) (hb : b.type = c.side)
    (hva : (RankTwo.graph F).Adj v a) (hvm : (RankTwo.graph F).Adj v m)
    (ham : a ≠ m)
    (hdbv : (RankTwo.graph F).dist b v ≤ 3)
    (hdbm : (RankTwo.graph F).dist b m ≤ 3)
    (hdba : (RankTwo.graph F).dist b a = 4) :
    ⁅c.label a, c.label b⁆ = c.label m := by
  let y := c.label b
  have hyv : y • v = v := c.fixes_ball b hb v (hr ▸ hdbv) (hdbv.trans (by omega))
  have hym : y • m = m := c.fixes_ball b hb m (hr ▸ hdbm) (hdbm.trans (by omega))
  have hya : y • a ≠ a := c.moves_sphere b hb (by omega) a (by omega)
  have hvya : (RankTwo.graph F).Adj v (y • a) := by
    have hh := (translationGraphIso F y).toHom.map_adj hva
    change (RankTwo.graph F).Adj (y • v) (y • a) at hh
    simpa only [hyv] using hh
  have hmya : m ≠ y • a := by
    intro he
    have haa : y • m = y • a := hym.trans he
    exact ham ((MulAction.toPerm y).injective haa).symm
  have hp := c.neighbor_product v a m (y • a) hva hvm hvya ham hya.symm hmya ha
  rw [c.conjugate y a ha] at hp
  have he : c.label a * c.label m = y * c.label a * y⁻¹ := by
    have hh := mul_eq_one_iff_eq_inv.mp hp
    simpa only [mul_inv_rev, inv_inv, c.label_inv ha, mul_assoc] using hh
  calc
    ⁅c.label a, c.label b⁆ = c.label a * (y * c.label a * y⁻¹) := by
      simp only [commutatorElement_def, c.label_inv ha, y, mul_assoc]
    _ = c.label a * (c.label a * c.label m) := by rw [← he]
    _ = c.label m := by
      rw [← mul_assoc, c.label_mul_self ha, one_mul]

/-- The literal midpoint commutator in Goldschmidt (6.9.1)(b). -/
theorem CanonicalLabelSetup.radiusTwo_commutator_distance_four
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {a b : RankTwo.Vertex F}
    (ha : a.type = c.side) (hb : b.type = c.side)
    (hd : (RankTwo.graph F).dist a b = 4) :
    ∃ m : RankTwo.Vertex F, (RankTwo.graph F).dist a m = 2 ∧
      (RankTwo.graph F).dist m b = 2 ∧ ⁅c.label a, c.label b⁆ = c.label m := by
  obtain ⟨p, hp⟩ := h.tree.connected.exists_walk_length_eq_dist a b
  have hp4 : p.length = 4 := hp.trans hd
  let m := p.getVert 2
  let v := p.getVert 1
  have hv : (RankTwo.graph F).Adj v a := by
    simpa only [Walk.getVert_zero] using (p.adj_getVert_succ (by omega : 0 < p.length)).symm
  have hvm : (RankTwo.graph F).Adj v m := p.adj_getVert_succ (by omega : 1 < p.length)
  have hbm : (RankTwo.graph F).dist b m ≤ 2 := by
    simpa only [Walk.length_reverse, Walk.drop_length, hp4] using dist_le (p.drop 2).reverse
  have hbv : (RankTwo.graph F).dist b v ≤ 3 := by
    simpa only [Walk.length_reverse, Walk.drop_length, hp4] using dist_le (p.drop 1).reverse
  have ham : (RankTwo.graph F).dist a m ≤ 2 := by
    simpa only [Walk.take_length, hp4, Nat.min_eq_left (by decide : 2 ≤ 4)] using dist_le (p.take 2)
  have htri := h.tree.connected.dist_triangle (u := a) (v := m) (w := b)
  rw [hd, SimpleGraph.dist_comm (u := m) (v := b)] at htri
  have ham2 : (RankTwo.graph F).dist a m = 2 := by omega
  have hmb2 : (RankTwo.graph F).dist m b = 2 := by
    rw [SimpleGraph.dist_comm]
    omega
  have hne : a ≠ m := by
    intro he
    simp only [he, SimpleGraph.dist_self] at ham2
    omega
  have hm : m.type = c.side := by
    have hh := (RankTwo.even_walk_iff F (p.take 2)).mp
      (by simp only [Walk.take_length, hp4]; decide)
    exact hh.symm.trans ha
  exact ⟨m, ham2, hmb2, c.radiusTwo_commutator_of_local_arc hr hs ha hm hb hv hvm
    hne hbv (hbm.trans (by decide)) (by rwa [SimpleGraph.dist_comm])⟩

/-- The source subgroup generated by the three labels neighboring a vertex. -/
def CanonicalLabelSetup.neighborLabelGroup (c : CanonicalLabelSetup F s)
    (v : RankTwo.Vertex F) : Subgroup G :=
  closure (c.label '' (RankTwo.graph F).neighborSet v)

private theorem label_triple_four {x y z : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hz : orderOf z = 2)
    (hp : x * y * z = 1) (hc : Commute x y) :
    IsKleinFour (closure ({x, y, z} : Set G)) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two, hz] using pow_orderOf_eq_one z)
  have hxy : x * y = z := by simpa only [hzi] using mul_eq_one_iff_eq_inv.mp hp
  have hne : x ≠ y := by
    rintro rfl
    have hx2 : x * x = 1 := by simpa only [pow_two, hx] using pow_orderOf_eq_one x
    have hz1 : z = 1 := hxy.symm.trans hx2
    simp only [hz1, orderOf_one] at hz
    omega
  have he : closure ({x, y, z} : Set G) = closure ({x, y} : Set G) := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · rw [← hxy]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · apply Subgroup.closure_mono
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      tauto
  rw [he]
  exact isKleinFour_closure_pair_of_orderOf x y hx hy hne hc

theorem CanonicalLabelSetup.radiusTwo_neighborLabelGroup_isKleinFour
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) (v : RankTwo.Vertex F) (hv : v.type ≠ c.side) :
    IsKleinFour (c.neighborLabelGroup v) := by
  have hcard : ((RankTwo.graph F).neighborSet v).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_neighbor v
  obtain ⟨a, b, d, hab, had, hbd, hneigh⟩ := Set.ncard_eq_three.mp hcard
  have ha : (RankTwo.graph F).Adj v a := by
    change a ∈ (RankTwo.graph F).neighborSet v
    rw [hneigh]; simp
  have hb : (RankTwo.graph F).Adj v b := by
    change b ∈ (RankTwo.graph F).neighborSet v
    rw [hneigh]; simp
  have hd : (RankTwo.graph F).Adj v d := by
    change d ∈ (RankTwo.graph F).neighborSet v
    rw [hneigh]; simp
  have hside {w : RankTwo.Vertex F} (hw : (RankTwo.graph F).Adj v w) : w.type = c.side := by
    have hn := hw.1
    cases ht : v.type <;> cases hw' : w.type <;> cases hc : c.side <;> simp_all
  have hdist : (RankTwo.graph F).dist a b ≤ 3 := by
    have hh := h.tree.connected.dist_triangle (u := a) (v := v) (w := b)
    rw [dist_eq_one_iff_adj.mpr ha.symm, dist_eq_one_iff_adj.mpr hb] at hh
    omega
  change IsKleinFour (closure (c.label '' (RankTwo.graph F).neighborSet v))
  rw [hneigh, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  exact label_triple_four (c.order_two a (hside ha)) (c.order_two b (hside hb))
    (c.order_two d (hside hd))
    (c.neighbor_product v a b d ha hb hd hab had hbd (hside ha))
    (c.radiusTwo_commute_of_dist_le_three hr hs (hside ha) (hside hb) hdist)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
