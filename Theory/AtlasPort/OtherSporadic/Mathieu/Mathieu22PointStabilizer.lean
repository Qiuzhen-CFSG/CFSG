/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.TransitiveNoncommutative
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Order

/-!
# Mathieu22PointStabilizer

The stabilizer of two distinct Golay coordinates acts faithfully and three-transitively
on the remaining twenty-two coordinates. Restriction and tuple orbit-stabilizer give its
actual embedding, order, indices, and further point-stabilizer orders.

Source: `Atlas/Mathieu/Mathieu22PointStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev Mathieu22PointModel (a : Omega) (b : Mathieu23Points a) :=
  MulAction.stabilizer (Mathieu23PointModel a) b
abbrev Mathieu22Points (a : Omega) (b : Mathieu23Points a) :=
  SubMulAction.ofStabilizer (Mathieu23PointModel a) b

instance mathieu22MulAction (a : Omega) (b : Mathieu23Points a) :
    MulAction (Mathieu22PointModel a b) (Mathieu22Points a b) :=
  SubMulAction.mulAction _

def mathieu22_to_mathieu23 (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PointModel a b →* Mathieu23PointModel a := (Mathieu22PointModel a b).subtype

def mathieu22_embedding (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PointModel a b →* Mathieu24CodeModel :=
  (mathieu23_embedding a).comp (mathieu22_to_mathieu23 a b)

theorem mathieu22_embedding_injective (a : Omega) (b : Mathieu23Points a) :
    Function.Injective (mathieu22_embedding a b) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem mathieu22_degree (a : Omega) (b : Mathieu23Points a) :
    Nat.card (Mathieu22Points a b) = 22 := by
  have h := SubMulAction.nat_card_ofStabilizer_add_one_eq (Mathieu23PointModel a) b
  rw [mathieu23_degree] at h
  change Nat.card (Mathieu22Points a b) + 1 = 23 at h
  omega

theorem mathieu22_faithful (a : Omega) (b : Mathieu23Points a) :
    FaithfulSMul (Mathieu22PointModel a b) (Mathieu22Points a b) := by
  have := mathieu23_faithful a
  exact Atlas.GroupTheory.stabilizer_complement_faithful b

theorem mathieu23_pretransitive (a : Omega) :
    MulAction.IsPretransitive (Mathieu23PointModel a) (Mathieu23Points a) := by
  have := mathieu23_four_transitive a
  have : MulAction.IsMultiplyPretransitive (Mathieu23PointModel a) (Mathieu23Points a) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4) (by rw [mathieu23_degree]; decide)
  exact MulAction.isPretransitive_of_is_two_pretransitive (G := Mathieu23PointModel a)
    (α := Mathieu23Points a)

theorem mathieu22_three_transitive (a : Omega) (b : Mathieu23Points a) :
    MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 3 := by
  have := mathieu23_pretransitive a
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := b)).mp (mathieu23_four_transitive a)

theorem mathieu22_not_four_transitive (a : Omega) (b : Mathieu23Points a) :
    ¬ MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 4 := by
  have := mathieu23_pretransitive a
  intro h
  exact mathieu23_not_five_transitive a
    ((SubMulAction.ofStabilizer.isMultiplyPretransitive (a := b)).mpr h)

def mathieu22_orbitEquiv (a : Omega) (b : Mathieu23Points a) :
    MulAction.orbit (Mathieu23PointModel a) b ≃ Mathieu23PointModel a ⧸ Mathieu22PointModel a b :=
  MulAction.orbitEquivQuotientStabilizer _ b

theorem mathieu22_order (a : Omega) (b : Mathieu23Points a) :
    Nat.card (Mathieu22PointModel a b) = 443520 := by
  let e : Fin 1 ↪ Mathieu23Points a := ⟨fun _ => b, fun _ _ _ => Subsingleton.elim _ _⟩
  have he : Set.range e = {b} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,hi⟩; exact hi.symm
    · intro hx; exact ⟨0,hx.symm⟩
  have hs : mathieu23TupleStabilizer a e = Mathieu22PointModel a b := by
    unfold mathieu23TupleStabilizer
    rw [he]
    ext g
    simp [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  rw [← hs]
  exact mathieu23_1_point_order a e

theorem mathieu22_index_product (a : Omega) (b : Mathieu23Points a) :
    23 * Nat.card (Mathieu22PointModel a b) = Nat.card (Mathieu23PointModel a) := by
  rw [mathieu22_order, mathieu23_order]

theorem mathieu22_ambient_index_product (a : Omega) (b : Mathieu23Points a) :
    24 * 23 * Nat.card (Mathieu22PointModel a b) = Nat.card Mathieu24CodeModel := by
  rw [mathieu22_order, mathieu24_order]

theorem mathieu22_order_factorization (a : Omega) (b : Mathieu23Points a) :
    Nat.card (Mathieu22PointModel a b) = 2^7 * 3^2 * 5 * 7 * 11 := by
  rw [mathieu22_order]
  norm_num

theorem mathieu22_image (a : Omega) (b : Mathieu23Points a) (g : Mathieu24CodeModel) :
    g ∈ (mathieu22_embedding a b).range ↔ g • a = a ∧ g • b.val = b.val := by
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨h.val.prop, congrArg Subtype.val h.prop⟩
  · rintro ⟨ha,hb⟩
    refine ⟨⟨⟨g,ha⟩,?_⟩,rfl⟩
    exact Subtype.ext hb


theorem mathieu22_noncommuting_pair (a : Omega) (b : Mathieu23Points a) :
    ∃ g h : Mathieu22PointModel a b, g * h ≠ h * g := by
  have := mathieu22_faithful a b
  have := mathieu22_three_transitive a b
  have : MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3) (by rw [mathieu22_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (Mathieu22Points a b) by
    rw [mathieu22_degree]; decide)).1
  apply Atlas.GroupTheory.noncommuting_of_card_ne_degree (G := Mathieu22PointModel a b) x
  rw [mathieu22_order, mathieu22_degree]
  decide

def mathieu22TupleStabilizer (a : Omega) (b : Mathieu23Points a) {k : ℕ}
    (e : Fin k ↪ Mathieu22Points a b) : Subgroup (Mathieu22PointModel a b) :=
  fixingSubgroup _ (Set.range e)

theorem mathieu22TupleStabilizer_order_product (a : Omega) (b : Mathieu23Points a) {k : ℕ}
    (e : Fin k ↪ Mathieu22Points a b) (hk : k ≤ 3) :
    Nat.card (mathieu22TupleStabilizer a b e) * ((22).choose k * k.factorial) = 443520 := by
  have := mathieu22_three_transitive a b
  have hn : (Set.range e).ncard = k := by
    rw [Set.ncard_range_of_injective e.injective]
    simp
  have ht : MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b)
      (Set.range e).ncard := by
    rw [hn]
    apply MulAction.isMultiplyPretransitive_of_le hk
    rw [mathieu22_degree]
    omega
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht
  rw [hn, mathieu22_degree] at hi
  have he := (mathieu22TupleStabilizer a b e).card_mul_index
  change (mathieu22TupleStabilizer a b e).index = (22).choose k * k.factorial at hi
  rw [hi, mathieu22_order] at he
  exact he

theorem mathieu22_one_point_order (a : Omega) (b : Mathieu23Points a)
    (e : Fin 1 ↪ Mathieu22Points a b) : Nat.card (mathieu22TupleStabilizer a b e) = 20160 := by
  have h := mathieu22TupleStabilizer_order_product a b e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

theorem mathieu22_two_point_order (a : Omega) (b : Mathieu23Points a)
    (e : Fin 2 ↪ Mathieu22Points a b) : Nat.card (mathieu22TupleStabilizer a b e) = 960 := by
  have h := mathieu22TupleStabilizer_order_product a b e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

theorem mathieu22_three_point_order (a : Omega) (b : Mathieu23Points a)
    (e : Fin 3 ↪ Mathieu22Points a b) : Nat.card (mathieu22TupleStabilizer a b e) = 48 := by
  have h := mathieu22TupleStabilizer_order_product a b e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

end Atlas.Codes
