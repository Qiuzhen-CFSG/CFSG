module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Quadrangle
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic

/-!
# Aligning the two marked endpoint ranges

A point-graph isomorphism maps the three points on an actual line to a
collinear triple, hence to another actual line. An equivariant group
isomorphism transports its stabilizer. Conjugating by a flag transporter
aligns both standard vertices simultaneously; equal native endpoint orders
upgrade the two resulting inclusions to exact range equalities.

This is the range-marked, quasiequivalence boundary of the U₄(2) case of
Aschbacher–Smith F.4.8 and F.4.24. It does not identify the endpoint injections
pointwise.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph.QuadrangleCollinearity
variable {G K : Type*} [Group G] [Group K] [Finite K]
variable (c : Completion G) (d : Completion K)

/-- A point-graph isomorphism sends the points of an actual line to points on a line. -/
theorem exists_line_image (hd : Nat.card K = 25920) (q : c.pointGraph ≃g d.pointGraph)
    (l : c.Vertex) (hl : l.type = false) :
    ∃ m : d.Vertex, m.type = false ∧
      ∀ x : c.Point, c.graph.Adj x.val l → d.graph.Adj (q x).val m := by
  obtain ⟨a, ha, _⟩ := c.hasTwoNeighbors l l
  obtain ⟨b, hb, hba⟩ := c.hasTwoNeighbors l a
  have hta : a.type = true := by simpa [hl] using c.adjacency_flip ha
  have htb : b.type = true := by simpa [hl] using c.adjacency_flip hb
  let x : c.Point := ⟨a, hta⟩
  let y : c.Point := ⟨b, htb⟩
  have hxy : x ≠ y := fun h => hba (congrArg Subtype.val h).symm
  obtain ⟨_, m, hxm, hym⟩ := q.map_rel_iff.mpr
    (show c.pointGraph.Adj x y from ⟨hxy, l, ha.symm, hb.symm⟩)
  have hm : m.type = false := by
    simpa only [(q x).property, Bool.not_true] using d.adjacency_flip hxm
  refine ⟨m, hm, ?_⟩
  intro z hz
  by_cases hzx : z = x
  · simpa only [hzx] using hxm
  by_cases hzy : z = y
  · simpa only [hzy] using hym
  obtain ⟨_, m₁, hxm₁, hzm₁⟩ := q.map_rel_iff.mpr
    (show c.pointGraph.Adj x z from ⟨fun h => hzx h.symm, l, ha.symm, hz⟩)
  obtain ⟨_, m₂, hym₂, hzm₂⟩ := q.map_rel_iff.mpr
    (show c.pointGraph.Adj y z from ⟨fun h => hzy h.symm, l, hb.symm, hz⟩)
  apply triangle_on_line (d.quadrangle_metric hd).1
    (fun h => hxy (q.injective (Subtype.ext h)))
    (fun h => hzy (q.injective (Subtype.ext h.symm)))
    (fun h => hzx (q.injective (Subtype.ext h)))
    hxm hym hxm₁ hzm₁ hym₂ hzm₂

/-- An equivariant point comparison carries the actual line stabilizer into its image line stabilizer. -/
theorem map_line_stabilizer_le (hd : Nat.card K = 25920)
    (q : c.pointGraph ≃g d.pointGraph) (e : G ≃* K)
    (he : ∀ g x, e g • q x = q (g • x))
    (l : c.Vertex) (hl : l.type = false) (m : d.Vertex)
    (hm : ∀ x : c.Point, c.graph.Adj x.val l → d.graph.Adj (q x).val m) :
    (stabilizer c.family l).map e.toMonoidHom ≤ stabilizer d.family m := by
  rintro _ ⟨g, hg, rfl⟩
  change e g • m = m
  obtain ⟨a, ha, _⟩ := c.hasTwoNeighbors l l
  obtain ⟨b, hb, hba⟩ := c.hasTwoNeighbors l a
  have hta : a.type = true := by simpa [hl] using c.adjacency_flip ha
  have htb : b.type = true := by simpa [hl] using c.adjacency_flip hb
  let x : c.Point := ⟨a, hta⟩
  let y : c.Point := ⟨b, htb⟩
  have hxy : x ≠ y := fun h => hba (congrArg Subtype.val h).symm
  have hxe : (e g • q x).val = (q (g • x)).val := congrArg Subtype.val (he g x)
  have hye : (e g • q y).val = (q (g • y)).val := congrArg Subtype.val (he g y)
  have hxl : c.graph.Adj (g • x).val l := by
    simpa only [point_smul_val, show g • l = l from hg] using c.graphAction.map_adj g ha.symm
  have hyl : c.graph.Adj (g • y).val l := by
    simpa only [point_smul_val, show g • l = l from hg] using c.graphAction.map_adj g hb.symm
  apply common_vertex_unique (d.quadrangle_metric hd).1
    (fun h => hxy ((MulAction.injective g) (q.injective (Subtype.ext h))))
    (show d.graph.Adj (q (g • x)).val (e g • m) from by
      simpa only [point_smul_val] using hxe ▸ d.graphAction.map_adj (e g) (hm x ha.symm))
    (show d.graph.Adj (q (g • y)).val (e g • m) from by
      simpa only [point_smul_val] using hye ▸ d.graphAction.map_adj (e g) (hm y hb.symm))
    (hm (g • x) hxl) (hm (g • y) hyl)

/-- Align the image of the standard incident flag, so both original endpoint
ranges agree with the two literal model endpoint ranges. -/
theorem exists_range_aligned (hd : Nat.card K = 25920)
    (q : c.pointGraph ≃g d.pointGraph) (e : G ≃* K)
    (he : ∀ g x, e g • q x = q (g • x)) :
    ∃ f : G ≃* K, c.left.range.map f.toMonoidHom = d.left.range ∧
      c.right.range.map f.toMonoidHom = d.right.range := by
  let l := RankTwo.base c.family false
  let p : c.Point := ⟨RankTwo.base c.family true, rfl⟩
  obtain ⟨m, hm, hqm⟩ := exists_line_image c d hd q l rfl
  have hp : c.graph.Adj p.val l := ⟨by change true ≠ false; decide, incident_base c.family true false⟩
  have hmp : d.graph.Adj m (q p).val := (hqm p hp).symm
  obtain ⟨k, hkl, hkp⟩ := incident_common_translate d.family hmp.2
  rw [hm] at hkl
  rw [(q p).property] at hkp
  let f : G ≃* K := e.trans (MulAut.conj k⁻¹)
  have htransport (i : Bool) (v : d.Vertex) (hv : k • RankTwo.base d.family i = v)
      (g : G) (hg : e g • v = v) : f g ∈ d.family i := by
    rw [← stabilizer_base d.family i]
    change (k⁻¹ * e g * (k⁻¹)⁻¹) • RankTwo.base d.family i = _
    rw [inv_inv, mul_smul, mul_smul, hv, hg, ← hv, inv_smul_smul]
  have hleft : c.left.range.map f.toMonoidHom ≤ d.left.range := by
    rintro _ ⟨g, hg, rfl⟩
    apply htransport false m hkl g
    have hmoved := map_line_stabilizer_le c d hd q e he l rfl m hqm
    apply hmoved
    exact Subgroup.mem_map.mpr ⟨g, by
      change g ∈ stabilizer c.family (RankTwo.base c.family false)
      simpa only [stabilizer, RankTwo.base, stabilizer_base, family_false, family_true, SetLike.mem_coe] using hg, rfl⟩
  have hright : c.right.range.map f.toMonoidHom ≤ d.right.range := by
    rintro _ ⟨g, hg, rfl⟩
    apply htransport true (q p).val hkp g
    have hgp : g • p = p := by
      apply Subtype.ext
      change g • RankTwo.base c.family true = RankTwo.base c.family true
      change g ∈ stabilizer c.family (RankTwo.base c.family true)
      simpa only [stabilizer, RankTwo.base, stabilizer_base, family_false, family_true, SetLike.mem_coe] using hg
    have hh := congrArg Subtype.val (he g p)
    simpa only [point_smul_val, hgp] using hh
  refine ⟨f, Subgroup.eq_of_le_of_card_ge hleft ?_, Subgroup.eq_of_le_of_card_ge hright ?_⟩
  · rw [Subgroup.card_map_of_injective f.injective, c.left_card, d.left_card]
  · rw [Subgroup.card_map_of_injective f.injective, c.right_card, d.right_card]

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
