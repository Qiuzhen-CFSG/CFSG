module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Setup
public import Theory.GroupAction.CubicTree.ArcRegularity
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Arc regularity in the original primitive cubic action

Goldschmidt's arcs are the existing nonbacktracking `BasedWalk`s in the literal
rank-two coset graph. Their stabilizers are the existing pointwise path fixers,
and their congruence relation is equality of the initial vertex type. The cubic
valences below come from the original two inclusion indices, rather than an
extra geometric assumption.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.12)--(2.13),
printed pp.383--384.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry

variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem graphAction : GraphAction (RankTwo.graph F) G :=
  ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩

/-- This uses the literal `pathStabilizer`, so later stabilizer generation
results act in the original ambient group. -/
theorem rightRegular_iff_pathStabilizer {n : ℕ} {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) :
    RightRegular (A := G) p ↔ ∀ z w, Theory.GroupAction.CubicTree.Forward p z →
      Theory.GroupAction.CubicTree.Forward p w →
        ∃ g ∈ RankTwo.pathStabilizer F p, g • z = w := Iff.rfl

theorem CubicTreeAction.card_neighbor (h : CubicTreeAction F) (v : RankTwo.Vertex F) :
    Nat.card ((RankTwo.graph F).neighborSet v) = 3 := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  have he : (RankTwo.graph F).neighborSet (RankTwo.base F v.type) ≃
      (RankTwo.graph F).neighborSet (g • RankTwo.base F v.type) :=
    (translationGraphIso F g).mapNeighborSet (RankTwo.base F v.type)
  rw [← hg, ← Nat.card_congr he, RankTwo.card_neighbor_base]
  cases hi : v.type with
  | false =>
    have hrange : (inclusionAmalgam (F false) (F true)).left.range =
        (F true).subgroupOf (F false) := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact b.property.2
      · intro ha
        exact ⟨⟨a, a.property, ha⟩, rfl⟩
    simpa only [hi, Bool.not_false, ← hrange] using h.primitive.left_index
  | true =>
    have hrange : (inclusionAmalgam (F false) (F true)).right.range =
        (F false).subgroupOf (F true) := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact b.property.1
      · intro ha
        exact ⟨⟨a, ha, a.property⟩, rfl⟩
    simpa only [hi, Bool.not_true, ← hrange] using h.primitive.right_index

theorem CubicTreeAction.zero_arc_regular (_h : CubicTreeAction F) (v : RankTwo.Vertex F) :
    RightRegular (Γ := RankTwo.graph F) (A := G) (n := 0) (x := v) PUnit.unit := by
  apply rightRegular_zero_of_neighbor_transitive
  intro x y z hxy hxz
  exact RankTwo.locally_transitive F hxy hxz

/-- Congruent arcs of length at most the first singular length are conjugate,
with the literal action on every vertex. This is (2.12)'s first conclusion. -/
theorem CubicTreeAction.congruent_arcs (_h : CubicTreeAction F) (s : ℕ)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {n : ℕ} (hn : n ≤ s) {v w : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (q : BasedWalk (RankTwo.graph F) n w)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking) (htype : v.type = w.type) :
    ∃ g : G, p.vertices.map (g • ·) = q.vertices :=
  arcTransitive_of_short_rightRegular graphAction s hshort hn p q hp hq
    ((RankTwo.same_orbit_iff F v w).2 htype)

theorem CubicTreeAction.card_nonbacktracking (h : CubicTreeAction F)
    (n : ℕ) (v : RankTwo.Vertex F) :
    Nat.card {p : BasedWalk (RankTwo.graph F) (n + 1) v // p.Nonbacktracking} =
      3 * 2 ^ n := by
  let : ∀ w : RankTwo.Vertex F, Finite ((RankTwo.graph F).neighborSet w) :=
    fun w => Nat.finite_of_card_ne_zero (by rw [h.card_neighbor w]; decide)
  have hflip : ∀ {a b : RankTwo.Vertex F}, (RankTwo.graph F).Adj a b → b.type = !a.type := by
    intro a b hab
    have hn := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  have hcount (k : ℕ) (b : Bool) : BasedWalk.forwardCount (fun _ => 3) k b = 2 ^ k := by
    induction k generalizing b with
    | zero => rfl
    | succ k ih => simp only [BasedWalk.forwardCount, ih, pow_succ]; omega
  rw [BasedWalk.card_nonbacktracking_succ (RankTwo.graph F) (·.type) (fun _ => 3)
    hflip (h.card_neighbor) n v, hcount]

/-- Local finiteness forces a failure of arc regularity: a finite vertex
stabilizer cannot act transitively on arbitrarily many nonbacktracking arcs. -/
theorem CubicTreeAction.exists_nonregular_arc (h : CubicTreeAction F) :
    ∃ n, ∃ v, ∃ p : BasedWalk (RankTwo.graph F) n v,
      p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  classical
  by_contra hall
  push Not at hall
  let v := RankTwo.base F false
  let d := Nat.card (RankTwo.stabilizer F v)
  let P := {p : BasedWalk (RankTwo.graph F) (d + 1) v // p.Nonbacktracking}
  let : MulAction (RankTwo.stabilizer F v) P :=
    RankTwo.nonbacktrackingAction F (d + 1) v
  let : ∀ i, Finite (F i) := h.finite
  have hcard : Nat.card P = 3 * 2 ^ d := h.card_nonbacktracking d v
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hne : Nonempty P := (Nat.card_pos_iff.mp (by rw [hcard]; positivity)).1
  obtain ⟨p⟩ := hne
  have ht : RootPathTransitive (RankTwo.graph F) G v (d + 1) :=
    rootPathTransitive_of_short_rightRegular graphAction (d + 1)
      (fun k w q _ hq => hall k w q hq) v (d + 1) le_rfl
  have htrans := (RankTwo.rootPathTransitive_iff F (d + 1) v).1 ht
  have hsur : Function.Surjective (fun a : RankTwo.stabilizer F v => a • p) := by
    intro q
    exact htrans.exists_smul_eq p q
  have hle : Nat.card P ≤ d := Nat.card_le_card_of_surjective _ hsur
  have hpow : d < 2 ^ d := Nat.lt_two_pow_self
  rw [hcard] at hle
  omega

/-- The first singular length exists for the original cubic action. The second
field supplies the hypothesis of the already proved congruent-arc theorem. -/
theorem CubicTreeAction.exists_singularityIndex (h : CubicTreeAction F) :
    ∃ s : ℕ, 0 < s ∧
      (∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
        k < s → p.Nonbacktracking → RightRegular (A := G) p) ∧
      ∃ v, ∃ p : BasedWalk (RankTwo.graph F) s v,
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  classical
  let hbad := h.exists_nonregular_arc
  let s := Nat.find hbad
  have hmin : ∀ k < s, ¬ ∃ v, ∃ p : BasedWalk (RankTwo.graph F) k v,
      p.Nonbacktracking ∧ ¬ RightRegular (A := G) p :=
    fun k hk => Nat.find_min hbad hk
  have hzero : s ≠ 0 := by
    intro hs
    have hbs : ∃ v, ∃ p : BasedWalk (RankTwo.graph F) s v,
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := Nat.find_spec hbad
    rw [hs] at hbs
    obtain ⟨v, p, hp, hn⟩ := hbs
    cases p
    exact hn (h.zero_arc_regular v)
  refine ⟨s, Nat.pos_of_ne_zero hzero, ?_, Nat.find_spec hbad⟩
  intro k v p hk hp
  by_contra hn
  exact hmin k hk ⟨v, p, hp, hn⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
