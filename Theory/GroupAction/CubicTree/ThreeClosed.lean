module

public import Theory.GroupTheory.Amalgam.ThreeClosed
public import Theory.GroupTheory.Amalgam.LocalCover
public import Theory.GroupAction.CubicTree.RegularityExistence
public import Theory.GroupAction.EvenPolygonFixedPoints

/-!
# Three-closed vertex stabilizers in faithful cubic actions

A subgroup fixing the endpoints of an edge vanishes when its normalizer
is transitive on the neighbors of both endpoints. Indeed the two normalizer
orbits cover the connected graph, and normalization preserves the fixed
vertex set. This supplies the kernel condition in the common overlap
conjugation calculation for a general graph action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.16)(b)
and its use in (5.3), printed pp.386 and 395.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

/-- A locally transitive normalizer of an edge fixer forces that fixer into
the kernel of the whole connected action. -/
theorem normalized_edge_subgroup_eq_bot [FaithfulSMul A V]
    (hact : GraphAction Γ A) (hconn : Γ.Preconnected) {x y : V}
    (K : Subgroup A) (hK : K ≤ MulAction.stabilizer A x ⊓ MulAction.stabilizer A y)
    (hx : ∀ z, Γ.Adj x z → ∃ a ∈ normalizer (K : Set A), a • y = z)
    (hy : ∀ z, Γ.Adj y z → ∃ a ∈ normalizer (K : Set A), a • x = z) : K = ⊥ := by
  let N := normalizer (K : Set A)
  let S (v : V) : Prop := (∃ a ∈ N, a • x = v) ∨ (∃ a ∈ N, a • y = v)
  have hstep {v w : V} (hvw : Γ.Adj v w) : S v → S w := by
    rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · have hadj : Γ.Adj x (a⁻¹ • w) := by
        simpa only [inv_smul_smul] using hact.map_adj a⁻¹ hvw
      obtain ⟨b, hb, he⟩ := hx _ hadj
      exact Or.inr ⟨a * b, N.mul_mem ha hb, by rw [mul_smul, he, smul_inv_smul]⟩
    · have hadj : Γ.Adj y (a⁻¹ • w) := by
        simpa only [inv_smul_smul] using hact.map_adj a⁻¹ hvw
      obtain ⟨b, hb, he⟩ := hy _ hadj
      exact Or.inl ⟨a * b, N.mul_mem ha hb, by rw [mul_smul, he, smul_inv_smul]⟩
  have hall (v : V) : S v := by
    obtain ⟨p⟩ := hconn x v
    have hp {a b : V} (q : Γ.Walk a b) : S a → S b := by
      induction q with
      | nil => exact id
      | cons hadj q ih => exact fun ha => ih (hstep hadj ha)
    exact hp p (Or.inl ⟨1, N.one_mem, one_smul A x⟩)
  apply le_bot_iff.mp
  intro k hk
  apply mem_bot.mpr
  apply eq_of_smul_eq_smul (α := V)
  intro v
  rw [one_smul]
  have hxfix : x ∈ GroupAction.EvenPolygon.fixedVertices K := fun _ hk => (hK hk).1
  have hyfix : y ∈ GroupAction.EvenPolygon.fixedVertices K := fun _ hk => (hK hk).2
  rcases hall v with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact GroupAction.EvenPolygon.normalizer_smul_mem_fixedVertices K ha hxfix k hk
  · exact GroupAction.EvenPolygon.normalizer_smul_mem_fixedVertices K ha hyfix k hk

private theorem neighbor_stabilizer_index
    (hact : GraphAction Γ A) (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z) {x y : V} (hxy : Γ.Adj x y) :
    (MulAction.stabilizer (MulAction.stabilizer A x) y).index = 3 := by
  have ho : MulAction.orbit (MulAction.stabilizer A x) y = Γ.neighborSet x := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      have he := hact.map_adj (a : A) hxy
      change Γ.Adj x ((a : A) • y)
      simpa only [show (a : A) • x = x from a.property] using he
    · intro hz
      obtain ⟨a, hax, hay⟩ := hlocal hxy hz
      exact ⟨⟨a, hax⟩, hay⟩
  rw [MulAction.index_stabilizer, ho]
  exact hcubic x

private theorem neighbor_stabilizer_isPGroup
    (hact : GraphAction Γ A) (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z) {x y : V} (hxy : Γ.Adj x y)
    (m : ℕ) (hcard : Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ m) :
    IsPGroup 2 (MulAction.stabilizer (MulAction.stabilizer A x) y) := by
  apply IsPGroup.of_card (n := m)
  have he := (MulAction.stabilizer (MulAction.stabilizer A x) y).card_mul_index
  rw [neighbor_stabilizer_index hact hcubic hlocal hxy, hcard] at he
  omega

private theorem cubic_moves_neighbors
    (hact : GraphAction Γ A) (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z) {x y : V} (hxy : Γ.Adj x y)
    [Finite (MulAction.stabilizer A x)]
    (m : ℕ) (hcard : Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ m)
    (X : Subgroup (MulAction.stabilizer A x)) (hX : Nat.card X = 3)
    (z : V) (hxz : Γ.Adj x z) :
    ∃ a ∈ X.map (MulAction.stabilizer A x).subtype, a • y = z := by
  let S := MulAction.stabilizer (MulAction.stabilizer A x) y
  have hcomp := three_complement_of_two_group_index_three S X
    (neighbor_stabilizer_isPGroup hact hcubic hlocal hxy m hcard)
    (neighbor_stabilizer_index hact hcubic hlocal hxy) hX
  obtain ⟨g, hgx, hgy⟩ := hlocal hxy hxz
  obtain ⟨⟨a, b⟩, he, _⟩ := hcomp.existsUnique (⟨g, hgx⟩ : MulAction.stabilizer A x)
  refine ⟨((a : MulAction.stabilizer A x) : A), ⟨a, a.property, rfl⟩, ?_⟩
  have he' := congrArg (fun u : MulAction.stabilizer A x => (u : A)) he
  change ((a : MulAction.stabilizer A x) : A) *
    ((b : MulAction.stabilizer A x) : A) = g at he'
  have hb : ((b : MulAction.stabilizer A x) : A) • y = y := b.property
  rw [← he', mul_smul, hb] at hgy
  exact hgy

/-- A normal Sylow three-subgroup forces the local order at most twelve.
The local order formula supplies the two-group edge stabilizers, so the
result applies directly to the actual quotient action of a regular arc group. -/
theorem local_card_le_twelve_of_normal_sylow_three [FaithfulSMul A V]
    (hact : GraphAction Γ A) (hconn : Γ.Preconnected)
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hvertex : ∀ x y : V, ∃ a : A, a • x = y)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z)
    (m : ℕ) (hcards : ∀ x : V, Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ m)
    (x : V) (P : Sylow 3 (MulAction.stabilizer A x))
    [(P : Subgroup (MulAction.stabilizer A x)).Normal] :
    Nat.card (MulAction.stabilizer A x) ≤ 12 := by
  let : ∀ z : V, Finite (MulAction.stabilizer A z) := fun z =>
    Nat.finite_of_card_ne_zero (by rw [hcards z]; positivity)
  obtain ⟨y⟩ := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Γ.neighborSet x) by rw [hcubic x]; decide)).1
  obtain ⟨a, ha⟩ := hvertex x y
  let e : MulAction.stabilizer A x ≃* MulAction.stabilizer A (y : V) :=
    MulAction.stabilizerEquivStabilizer ha.symm
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : (Q : Subgroup (MulAction.stabilizer A (y : V))).Normal :=
    (inferInstance : (P : Subgroup (MulAction.stabilizer A x)).Normal).map
      e.toMonoidHom e.surjective
  have hP : Nat.card P = 3 := card_sylow_three_of_two_group_index_three
    (MulAction.stabilizer (MulAction.stabilizer A x) (y : V))
    (neighbor_stabilizer_isPGroup hact hcubic hlocal y.property m (hcards x))
    (neighbor_stabilizer_index hact hcubic hlocal y.property) P
  have hQ : Nat.card Q = 3 := card_sylow_three_of_two_group_index_three
    (MulAction.stabilizer (MulAction.stabilizer A (y : V)) x)
    (neighbor_stabilizer_isPGroup hact hcubic hlocal y.property.symm m (hcards y))
    (neighbor_stabilizer_index hact hcubic hlocal y.property.symm) Q
  have hE : Nat.card (MulAction.stabilizer A x ⊓ MulAction.stabilizer A (y : V) :
      Subgroup A) ≤ 4 := by
    apply Subgroup.overlap_card_le_four_of_normal_three _ _
      (P : Subgroup (MulAction.stabilizer A x))
      (Q : Subgroup (MulAction.stabilizer A (y : V))) hP hQ
    intro K hK hPK hQK
    apply normalized_edge_subgroup_eq_bot hact hconn K hK
    · intro z hxz
      obtain ⟨b, hb, he⟩ := cubic_moves_neighbors hact hcubic hlocal y.property m
        (hcards x) (P : Subgroup (MulAction.stabilizer A x)) hP z hxz
      exact ⟨b, hPK hb, he⟩
    · intro z hyz
      obtain ⟨b, hb, he⟩ := cubic_moves_neighbors hact hcubic hlocal y.property.symm m
        (hcards y) (Q : Subgroup (MulAction.stabilizer A (y : V))) hQ z hyz
      exact ⟨b, hQK hb, he⟩
  let S := MulAction.stabilizer (MulAction.stabilizer A x) (y : V)
  have hc : Nat.card S = Nat.card
      (MulAction.stabilizer A x ⊓ MulAction.stabilizer A (y : V) : Subgroup A) := by
    let eS : S ≃ (MulAction.stabilizer A x ⊓ MulAction.stabilizer A (y : V) :
        Subgroup A) := {
      toFun u := ⟨u.val, u.val.property, u.property⟩
      invFun u := ⟨⟨u, u.property.1⟩, u.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact Nat.card_congr eS
  have he := S.card_mul_index
  rw [neighbor_stabilizer_index hact hcubic hlocal y.property, hc] at he
  omega

/-- Regularity length at least four excludes a normal local Sylow three.
This is the three-closed exclusion needed in Goldschmidt (5.3), without a
general upper bound on the regularity length. -/
theorem not_normal_sylow_three_of_regularity_at_least_four [FaithfulSMul A V]
    (hact : GraphAction Γ A) (hconn : Γ.Preconnected)
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hvertex : ∀ x y : V, ∃ a : A, a • x = y)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z)
    (s : ℕ) (hs : 4 ≤ s)
    (hcards : ∀ x : V, Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ (s - 1))
    (x : V) (P : Sylow 3 (MulAction.stabilizer A x)) :
    ¬ (P : Subgroup (MulAction.stabilizer A x)).Normal := by
  intro hP
  let := hP
  have hbound := local_card_le_twelve_of_normal_sylow_three hact hconn hcubic
    hvertex hlocal (s - 1) hcards x P
  rw [hcards x] at hbound
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ s - 1 by omega)
  norm_num at hp
  omega

end Theory.GroupAction.CubicTree
