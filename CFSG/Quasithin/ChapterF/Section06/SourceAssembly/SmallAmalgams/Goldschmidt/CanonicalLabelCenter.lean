module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelElementary
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreIndex

/-!
# The central line in a canonical label group

A central involution of a vertex stabilizer belongs to its two-core, hence
to each incident edge stabilizer. The cyclic edge center identifies it with
the canonical label. Consequently the centralizer of the vertex stabilizer
inside the elementary radius-two label group is exactly that label's line.
This is the literal central-element alternative used after (6.12.1).

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.8) and (6.12.1)--(6.12.3), pp.399 and 403--404.
-/

public section
open Subgroup SimpleGraph Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- Every involution central in an actual vertex stabilizer is the label at
that vertex. Finiteness is required only for the stabilizers. -/
theorem CanonicalLabelSetup.eq_label_of_central_vertex
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hs : 1 ≤ s)
    {a : RankTwo.Vertex F} (ha : a.type = d.side) {z : G}
    (hz : orderOf z = 2) (hza : z ∈ RankTwo.stabilizer F a)
    (hc : ∀ g ∈ RankTwo.stabilizer F a, Commute z g) : z = d.label a := by
  let H := RankTwo.stabilizer F a
  let zH : H := ⟨z, hza⟩
  have hzH : orderOf zH = 2 := (Subgroup.orderOf_coe zH).symm.trans hz
  have hzC : zH ∈ Subgroup.center H := mem_center_iff.mpr fun x =>
    Subtype.ext (hc x x.property).symm.eq
  have hZ : zpowers zH ≤ Subgroup.center H := zpowers_le.mpr hzC
  let : (zpowers zH).Normal := ⟨by
    intro x hx g
    have he := mem_center_iff.mp (hZ hx) g
    simpa only [he, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  have hp : IsPGroup 2 (zpowers zH) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hzH, pow_one])
  have hzcore : zH ∈ pCore 2 H :=
    (show zpowers zH ≤ pCore 2 H from le_sSup ⟨inferInstance, hp⟩) (mem_zpowers zH)
  obtain ⟨f⟩ := h.exists_branchFrame a
  let b := (f.e 0).val
  have hab : (RankTwo.graph F).Adj a b := (f.e 0).property
  have hzedge : z ∈ RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b := by
    have hm : z ∈ (pCore 2 H).map H.subtype := ⟨zH, hzcore, rfl⟩
    have hh := h.vertexTwoCore_le_edge hab.symm hm
    exact ⟨hh.2, hh.1⟩
  exact d.eq_label_of_central_edge h hs hab ha hz hzedge
    (fun g hg => hc g hg.1)

/-- The central square-one elements at a labeled vertex are exactly one and
the canonical label. No description of the whole local center is assumed. -/
theorem CanonicalLabelSetup.eq_one_or_label_of_central_vertex
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hs : 1 ≤ s)
    {a : RankTwo.Vertex F} (ha : a.type = d.side) {z : G}
    (hz : z ^ 2 = 1) (hza : z ∈ RankTwo.stabilizer F a)
    (hc : ∀ g ∈ RankTwo.stabilizer F a, Commute z g) : z = 1 ∨ z = d.label a := by
  by_cases he : z = 1
  · exact Or.inl he
  · exact Or.inr (d.eq_label_of_central_vertex h hs ha (orderOf_eq_prime hz he) hza hc)

/-- In the source radius-two label group, the only elements centralizing the
full vertex stabilizer lie on its canonical line. -/
theorem CanonicalLabelSetup.radiusTwo_inter_centralizer
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : 3 ≤ d.radius) (hs : 4 ≤ s)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    d.labelBall a 2 ⊓ centralizer (RankTwo.stabilizer F a : Set G) =
      zpowers (d.label a) := by
  let : IsElementaryAbelian 2 (d.labelBall a 2) :=
    d.labelBall_elementary h a 2 (by omega) hs
  apply le_antisymm
  · intro z hz
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1
    have hmem := d.labelBall_le_stabilizer a 2 (by omega) (by omega) hz.1
    rcases d.eq_one_or_label_of_central_vertex h (by omega) ha hpow hmem
        (fun g hg => (show Commute g z from hz.2 g hg).symm) with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · apply zpowers_le.mpr
    refine ⟨d.label_mem_labelBall ha (by simp), ?_⟩
    intro g hg
    exact ((d.central a ha).2 g hg).symm.eq

/-- The central correction in (6.12.1) is either one or the center label.
Its exponent is obtained from the actual elementary label group. -/
theorem CanonicalLabelSetup.radiusTwo_central_element
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : 3 ≤ d.radius) (hs : 4 ≤ s)
    {a : RankTwo.Vertex F} (ha : a.type = d.side) {v : G}
    (hv : v ∈ d.labelBall a 2)
    (hc : ∀ g ∈ RankTwo.stabilizer F a, Commute v g) :
    v = 1 ∨ v = d.label a := by
  let : IsElementaryAbelian 2 (d.labelBall a 2) :=
    d.labelBall_elementary h a 2 (by omega) hs
  exact d.eq_one_or_label_of_central_vertex h (by omega) ha
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
    (d.labelBall_le_stabilizer a 2 (by omega) (by omega) hv) hc

/-- Once the source commutator correction is central and the one-label case
has been excluded, the six-arc commutator has the required two-label value.
This is the final implication from (6.12.1) to (6.12.3), with the original
centers and actual radius-two group retained. -/
theorem CanonicalLabelSetup.radiusTwo_central_correction
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : 3 ≤ d.radius) (hs : 4 ≤ s)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side) (hb : b.type = d.side)
    (hab : (RankTwo.graph F).dist a b ≤ 2) {u : G}
    (hu : u ∈ d.labelBall a 2) (hne : u ≠ d.label b)
    (hc : ∀ g ∈ RankTwo.stabilizer F a, Commute (u * d.label b) g) :
    u = d.label a * d.label b := by
  have hv := (d.labelBall a 2).mul_mem hu (d.label_mem_labelBall hb hab)
  rcases d.radiusTwo_central_element h hr hs ha hv hc with hone | hlabel
  · exact (hne (by simpa only [d.label_inv hb] using mul_eq_one_iff_eq_inv.mp hone)).elim
  · calc
      u = u * (d.label b * d.label b) := by rw [d.label_mul_self hb, mul_one]
      _ = d.label a * d.label b := by rw [← mul_assoc, hlabel]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
