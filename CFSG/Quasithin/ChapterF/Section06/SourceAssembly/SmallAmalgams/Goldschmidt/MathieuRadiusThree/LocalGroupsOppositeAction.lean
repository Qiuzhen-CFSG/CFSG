module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeGenerators

/-!
# The order of the adjacent generators of the opposite endpoint

The radius-four group is transitive on the three neighbours of its labelled
centre: its transitive action on the second sphere descends to the three
branches. Thus its stabilizer of an adjacent unlabelled vertex has index
three. This identifies the order-64 groups used on printed p.406 directly
inside the source action once the radius-four order is known.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.6), printed pp.405--406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The literal radius-four group, not just the original vertex stabilizer,
is transitive on the three branches at its labelled centre. -/
theorem LocalRelations.radiusFour_neighbor_transitive
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {a v w : RankTwo.Vertex F} (ha : a.type = d.side)
    (hv : (RankTwo.graph F).Adj a v) (hw : (RankTwo.graph F).Adj a w) :
    ∃ k ∈ d.labelBall a 4, k • v = w := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame a
  obtain ⟨i, hi⟩ := f.e.surjective ⟨v, hv⟩
  obtain ⟨j, hj⟩ := f.e.surjective ⟨w, hw⟩
  have hi' : (f.e i).val = v := congrArg Subtype.val hi
  have hj' : (f.e j).val = w := congrArg Subtype.val hj
  obtain ⟨k, hk, he⟩ := r.radiusFour_sphere_transitive hr ha f (i,0) (j,0)
  have hp : f.sphereAction t k (i,0) = (j,0) :=
    f.point_injective t ((f.sphereAction_eval t k (i,0)).trans he)
  have hb : f.branchAction k i = j := by
    rw [← f.sphereAction_block t k (i,0), hp]
  refine ⟨k.val, hk, ?_⟩
  rw [← hi', ← f.branchAction_eval k i, hb, hj']

/-- The adjacent stabilizer has index three in the actual radius-four group. -/
theorem LocalRelations.oppositeGenerator_card_mul_three
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {a v : RankTwo.Vertex F} (ha : a.type = d.side)
    (hv : (RankTwo.graph F).Adj v a) :
    Nat.card (oppositeGenerator d v a) * 3 = Nat.card (d.labelBall a 4) := by
  let t := h.action.toCubicTreeAction
  let K := d.labelBall a 4
  have hK : K ≤ RankTwo.stabilizer F a :=
    d.labelBall_le_stabilizer a 4 (by omega) (by have := h.five_le; omega)
  have horbit : MulAction.orbit K v = (RankTwo.graph F).neighborSet a := by
    ext w
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hw
      change (RankTwo.graph F).Adj a (k.val • v)
      have hh := (translationGraphIso F k.val).toHom.map_adj hv.symm
      change (RankTwo.graph F).Adj (k.val • a) (k.val • v) at hh
      simpa only [show k.val • a = a from hK k.property] using hh
    · intro hw
      obtain ⟨k, hk, he⟩ := r.radiusFour_neighbor_transitive hr ha hv.symm hw
      exact MulAction.mem_orbit_iff.mpr ⟨⟨k, hk⟩, he⟩
  have ho : Nat.card (MulAction.orbit K v) = 3 :=
    (Nat.card_congr (Equiv.setCongr horbit)).trans (t.card_neighbor a)
  let e : MulAction.stabilizer K v ≃* oppositeGenerator d v a := {
    toFun := fun k => ⟨k.val.val, k.val.property, k.property⟩
    invFun := fun k => ⟨⟨k.val, k.property.1⟩, k.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K v)
  rw [Nat.card_prod, ho, Nat.card_congr e.toEquiv, Nat.mul_comm] at hc
  exact hc

/-- The known radius-four order makes each literal arm group order64. -/
theorem LocalRelations.oppositeGenerator_card_of_radiusFour_card
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {a v : RankTwo.Vertex F} (ha : a.type = d.side)
    (hv : (RankTwo.graph F).Adj v a)
    (hc : Nat.card (d.labelBall a 4) = 192) :
    Nat.card (oppositeGenerator d v a) = 64 := by
  have hh := r.oppositeGenerator_card_mul_three hr ha hv
  omega

/-- The arm group at `a` exchanges the other two neighbours of `v`.
The actor is chosen in the actual radius-four group using its second-sphere
transitivity; uniqueness of the tree midpoint makes it fix `v`. -/
theorem LocalRelations.oppositeGenerator_neighbor_transitive
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {v a b c : RankTwo.Vertex F} (ha : a.type = d.side)
    (hva : (RankTwo.graph F).Adj v a)
    (hvb : (RankTwo.graph F).Adj v b) (hvc : (RankTwo.graph F).Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) :
    ∃ k ∈ oppositeGenerator d v a, k • b = c := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame a
  have hb : (RankTwo.graph F).dist a b = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr ⟨hab, v, hva.symm, hvb⟩
  have hc : (RankTwo.graph F).dist a c = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr ⟨hac, v, hva.symm, hvc⟩
  obtain ⟨x, hx⟩ := (f.sphereEquiv t).surjective ⟨b, hb⟩
  obtain ⟨y, hy⟩ := (f.sphereEquiv t).surjective ⟨c, hc⟩
  have hx' : f.point x = b := congrArg Subtype.val hx
  have hy' : f.point y = c := congrArg Subtype.val hy
  obtain ⟨k, hk, he⟩ := r.radiusFour_sphere_transitive hr ha f x y
  have hbc : k.val • b = c := by simpa only [hx', hy'] using he
  have hkv : k.val • v = v := by
    apply DistanceTwoGeometry.midpoint_unique t.tree.isAcyclic hac
    · have hh := (translationGraphIso F k.val).toHom.map_adj hva.symm
      change (RankTwo.graph F).Adj (k.val • a) (k.val • v) at hh
      simpa only [show k.val • a = a from k.property] using hh
    · have hh := (translationGraphIso F k.val).toHom.map_adj hvb
      change (RankTwo.graph F).Adj (k.val • v) (k.val • b) at hh
      simpa only [hbc] using hh
    · exact hva.symm
    · exact hvc
  exact ⟨k.val, ⟨hk, hkv⟩, hbc⟩

/-- The literal generated opposite group is locally transitive, before
identifying either endpoint or assuming the order of the generated group. -/
theorem LocalRelations.oppositeGroup_neighbor_transitive
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {v b c : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (hb : (RankTwo.graph F).Adj v b) (hc : (RankTwo.graph F).Adj v c) :
    ∃ k ∈ oppositeGroup d v, k • b = c := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame v
  obtain ⟨i, hi⟩ := f.e.surjective ⟨b, hb⟩
  obtain ⟨j, hj⟩ := f.e.surjective ⟨c, hc⟩
  obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 3)
  let a := (f.e l).val
  have ha : a.type = d.side := by
    have hn : v.type ≠ a.type := (f.e l).property.1
    cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all
  have hab : a ≠ b := by
    intro he
    apply hli
    exact f.e.injective ((Subtype.ext he).trans hi.symm)
  have hac : a ≠ c := by
    intro he
    apply hlj
    exact f.e.injective ((Subtype.ext he).trans hj.symm)
  obtain ⟨k, hk, he⟩ := r.oppositeGenerator_neighbor_transitive hr ha
    (f.e l).property hb hc hab hac
  exact ⟨k, oppositeGenerator_le d (f.e l).property hk, he⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
