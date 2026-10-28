module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits.FullRee
/-!
# The literal full binary Ree completion in F.4.8 and J.4.7

Faithful maps from the two concrete full Ree parabolics define the completion.
Their orders force the common image to be the whole intersection. The induced
coset graph is connected and bipartite, with valences five and three at the
original two types. Smallness is precisely nonuniqueness of an eight-edge
geodesic. Moving a vertex of such a geodesic while fixing its endpoints is a
sufficient condition, matching the last argument of J.4.10.

The source constructor transports a compatible identification of the literal
inclusion amalgam and retains its original coset graph. It does not assume a
recognition conclusion, finite group order, or polygon certificate. These are
the boundary and local facts for F.4.8; the geometric reconstruction of a small
completion as the full group `ReeF4.Model 0` remains a separate theorem.

Source: Aschbacher--Smith, F.4.4--8, printed pp.274--278, and the proof of J.4.7,
including J.4.10, printed pp.442--445.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Theory.GroupTheory
open Subgroup.CosetGeometry
open Subgroup.CosetGeometry.RankTwo
local notation "ModelAmalgam" => Tits.ExceptionalParabolics.FullRee.amalgam

/-- A faithful completion of the actual marked full binary Ree amalgam. -/
abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion ModelAmalgam (G := G)

variable {G : Type*} [Group G] (c : Completion G)
namespace Completion
/-- The Suzuki and linear endpoint images, in the source order. -/
def family : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family

@[simp] theorem family_false : c.family false = c.left.range := rfl
@[simp] theorem family_true : c.family true = c.right.range := rfl

theorem left_card : Nat.card c.left.range = 20480 :=
  (RankTwoAmalgam.FaithfulCompletion.left_card c).trans Tits.ExceptionalParabolics.FullRee.first_card
theorem right_card : Nat.card c.right.range = 12288 :=
  (RankTwoAmalgam.FaithfulCompletion.right_card c).trans Tits.ExceptionalParabolics.FullRee.second_card
theorem middle_card : Nat.card c.middle.range = 4096 :=
  (RankTwoAmalgam.FaithfulCompletion.middle_card c).trans Tits.ExceptionalParabolics.FullRee.borel_card

/-- Faithfulness already forces the overlap required for the actual coset graph. -/
theorem overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  apply c.overlap_eq_of_gcd
  rw [Tits.ExceptionalParabolics.FullRee.first_card,
    Tits.ExceptionalParabolics.FullRee.second_card,
    Tits.ExceptionalParabolics.FullRee.borel_card]
  norm_num

theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

theorem bipartite : c.graph.IsBipartiteWith
    {v : c.Vertex | v.type = false} {v : c.Vertex | v.type = true} :=
  coset_bipartition c.family

theorem graphAction : SimpleGraph.PathTransitivePolygon.GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

/-- Both local indices are forced by the original full parabolic orders. -/
theorem local_indices :
    (c.right.range.subgroupOf c.left.range).index = 5 ∧
    (c.left.range.subgroupOf c.right.range).index = 3 := by
  have hleft : Nat.card (c.right.range.subgroupOf c.left.range) = 4096 := by
    rw [← Subgroup.inf_subgroupOf_left, c.overlap]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.middle_le_left).toEquiv).trans
      (middle_card c)
  have hright : Nat.card (c.left.range.subgroupOf c.right.range) = 4096 := by
    rw [← Subgroup.inf_subgroupOf_right, c.overlap]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.middle_le_right).toEquiv).trans
      (middle_card c)
  have hl := (c.right.range.subgroupOf c.left.range).card_mul_index
  have hr := (c.left.range.subgroupOf c.right.range).card_mul_index
  rw [hleft, left_card c] at hl
  rw [hright, right_card c] at hr
  constructor <;> omega

theorem neighbor_cards :
    Nat.card (c.graph.neighborSet (RankTwo.base c.family false)) = 5 ∧
    Nat.card (c.graph.neighborSet (RankTwo.base c.family true)) = 3 := by
  constructor
  · exact (card_neighbor_base c.family false).trans (local_indices c).1
  · exact (card_neighbor_base c.family true).trans (local_indices c).2

/-- Valence is five or three at every vertex of its respective type. -/
theorem card_neighbors (v : c.Vertex) :
    Nat.card (c.graph.neighborSet v) = (if v.type then 3 else 5) := by
  obtain ⟨g, hg⟩ := exists_smul_base c.family v
  have hh := Nat.card_congr
    ((translationGraphIso c.family g).mapNeighborSet (RankTwo.base c.family v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.family v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.family v.type)) at hh
  rw [hg] at hh
  rw [← hh]
  cases hv : v.type
  · exact (neighbor_cards c).1
  · exact (neighbor_cards c).2

/-- Thickness in the literal graph, as required by path-extension arguments. -/
theorem thick (v a b : c.Vertex) : ∃ z, c.graph.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card (c.graph.neighborSet v) := by
    rw [card_neighbors c v]
    cases v.type <;> decide
  have : Finite (c.graph.neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (c.graph.neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all

/-- Literal F.4.7 smallness: two different shortest eight-edge walks between
one pair of opposite vertices. No finiteness or recognition conclusion is built in. -/
def Small : Prop := ∃ x y : c.Vertex, c.graph.dist x y = 8 ∧
  ∃ p q : c.graph.Walk x y, p.length = 8 ∧ q.length = 8 ∧ p ≠ q

theorem small_iff_distinct_geodesics : c.Small ↔
    ∃ x y : c.Vertex, c.graph.dist x y = 8 ∧
      ∃ p q : c.graph.Walk x y, p.IsPath ∧ q.IsPath ∧
        p.length = c.graph.dist x y ∧ q.length = c.graph.dist x y ∧ p ≠ q := by
  constructor
  · rintro ⟨x, y, hd, p, q, hp, hq, hpq⟩
    exact ⟨x, y, hd, p, q, p.isPath_of_length_eq_dist (hp.trans hd.symm),
      q.isPath_of_length_eq_dist (hq.trans hd.symm), hp.trans hd.symm,
      hq.trans hd.symm, hpq⟩
  · rintro ⟨x, y, hd, p, q, _, _, hp, hq, hpq⟩
    exact ⟨x, y, hd, p, q, hp.trans hd, hq.trans hd, hpq⟩
/-- The final J.4.10 argument supplies an element fixing the two endpoints
but moving a vertex on a geodesic. Its translated walk proves smallness. -/
theorem small_of_moves_walk (x y : c.Vertex) (hd : c.graph.dist x y = 8)
    (p : c.graph.Walk x y) (hp : p.length = 8) (g : G)
    (hx : g • x = x) (hy : g • y = y) (i : ℕ)
    (hm : g • p.getVert i ≠ p.getVert i) : c.Small := by
  let q : c.graph.Walk x y := (p.map ((graphAction c).hom g)).copy hx hy
  refine ⟨x, y, hd, p, q, hp, ?_, ?_⟩
  · exact ((p.map ((graphAction c).hom g)).length_copy hx hy).trans
      ((p.length_map ((graphAction c).hom g)).trans hp)
  · intro he
    have hv := congrArg (fun r : c.graph.Walk x y => r.getVert i) he.symm
    have hv' : (p.map ((graphAction c).hom g)).getVert i = p.getVert i :=
      ((p.map ((graphAction c).hom g)).getVert_copy i hx hy).symm.trans hv
    exact hm ((p.getVert_map ((graphAction c).hom g) i).symm.trans hv')

end Completion

/-- The J.4.5 source input is a compatible identification of the literal local
inclusions, not three unrelated abstract group isomorphisms. -/
def ofSource (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    Completion G :=
  (RankTwoAmalgam.FaithfulCompletion.ofSubgroups P₁ T P₂ h₁ h₂ hgen).comapIso e.symm

@[simp] theorem ofSource_left_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    (ofSource P₁ T P₂ h₁ h₂ hgen e).left.range = P₁ := by
  simp [ofSource]

@[simp] theorem ofSource_right_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    (ofSource P₁ T P₂ h₁ h₂ hgen e).right.range = P₂ := by
  simp [ofSource]

@[simp] theorem ofSource_middle_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    (ofSource P₁ T P₂ h₁ h₂ hgen e).middle.range = T := by
  simp [ofSource]

/-- The actual source intersection follows from its compatible model marking. -/
theorem ofSource_overlap (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    P₁ ⊓ P₂ = T := by
  simpa only [ofSource_left_range, ofSource_right_range, ofSource_middle_range] using
    Completion.overlap (ofSource P₁ T P₂ h₁ h₂ hgen e)

/-- The completion uses the original source coset graph, with no new action. -/
theorem ofSource_family (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam) :
    (ofSource P₁ T P₂ h₁ h₂ hgen e).family = (fun i => bif i then P₂ else P₁) := by
  funext i
  cases i <;> simp

/-- Actual J.4.7 boundary: its two source geodesics establish precisely F.4.7
smallness of the full binary Ree completion. -/
theorem ofSource_small (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) ModelAmalgam)
    (x y : RankTwo.Vertex (fun i => bif i then P₂ else P₁))
    (hd : (RankTwo.graph (fun i => bif i then P₂ else P₁)).dist x y = 8)
    (p q : (RankTwo.graph (fun i => bif i then P₂ else P₁)).Walk x y)
    (hp : p.length = 8) (hq : q.length = 8) (hpq : p ≠ q) :
    (ofSource P₁ T P₂ h₁ h₂ hgen e).Small := by
  unfold Completion.Small Completion.graph Completion.Vertex
  rw [ofSource_family]
  exact ⟨x, y, hd, p, q, hp, hq, hpq⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
