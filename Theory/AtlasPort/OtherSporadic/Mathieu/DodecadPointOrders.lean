/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu12SharpAction

/-!
# DodecadPointOrders

Sharp five-transitivity determines the orders of dodecad pointwise stabilizers through
five points. The tuple orbit-stabilizer formula gives the counts and rules out six-
transitivity.

Source: `Atlas/Mathieu/DodecadPointOrders.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def dodecadOrderedStabilizer (D : Dodecad) {k : ℕ} (e : Fin k ↪ Mathieu12Points D) :
    Subgroup (Mathieu12DodecadModel D) := fixingSubgroup (Mathieu12DodecadModel D) (Set.range e)

theorem dodecadOrderedStabilizer_order_product (D : Dodecad) {k : ℕ}
    (e : Fin k ↪ Mathieu12Points D) (hk : k ≤ 5) :
    Nat.card (dodecadOrderedStabilizer D e) * ((12).choose k * k.factorial) = 95040 := by
  let := mathieu12_five_transitive D
  have hn : (Set.range e).ncard = k := by
    rw [Set.ncard_range_of_injective e.injective]
    simp
  have ht : MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D)
      (Mathieu12Points D) (Set.range e).ncard := by
    rw [hn]
    apply MulAction.isMultiplyPretransitive_of_le hk
    rw [mathieu12_degree]
    omega
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht
  rw [hn,mathieu12_degree] at hi
  have he := (dodecadOrderedStabilizer D e).card_mul_index
  change (dodecadOrderedStabilizer D e).index = Nat.choose 12 k * k.factorial at hi
  rw [hi,mathieu12_order] at he
  exact he

theorem mathieu12_four_point_order (D : Dodecad) (e : Fin 4 ↪ Mathieu12Points D) :
    Nat.card (dodecadOrderedStabilizer D e) = 8 := by
  have he := dodecadOrderedStabilizer_order_product D e (by decide)
  norm_num [Nat.choose,Nat.factorial] at he
  omega

theorem mathieu12_one_point_order (D : Dodecad) (e : Fin 1 ↪ Mathieu12Points D) :
    Nat.card (dodecadOrderedStabilizer D e) = 7920 := by
  have he := dodecadOrderedStabilizer_order_product D e (by decide)
  norm_num [Nat.choose,Nat.factorial] at he
  omega

theorem mathieu12_two_point_order (D : Dodecad) (e : Fin 2 ↪ Mathieu12Points D) :
    Nat.card (dodecadOrderedStabilizer D e) = 720 := by
  have he := dodecadOrderedStabilizer_order_product D e (by decide)
  norm_num [Nat.choose,Nat.factorial] at he
  omega

theorem mathieu12_three_point_order (D : Dodecad) (e : Fin 3 ↪ Mathieu12Points D) :
    Nat.card (dodecadOrderedStabilizer D e) = 72 := by
  have he := dodecadOrderedStabilizer_order_product D e (by decide)
  norm_num [Nat.choose,Nat.factorial] at he
  omega

theorem mathieu12_five_point_order (D : Dodecad) (e : Fin 5 ↪ Mathieu12Points D) :
    Nat.card (dodecadOrderedStabilizer D e) = 1 := by
  have he := dodecadOrderedStabilizer_order_product D e (by decide)
  norm_num [Nat.choose,Nat.factorial] at he
  simp [he]

theorem mathieu12_not_six_transitive (D : Dodecad) :
    ¬ MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) 6 := by
  intro ht
  classical
  obtain ⟨e⟩ : Nonempty (Fin 6 ↪ Mathieu12Points D) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin,← Nat.card_eq_fintype_card,mathieu12_degree]; omega)
  have hn : (Set.range e).ncard = 6 := by
    rw [Set.ncard_range_of_injective e.injective]; simp
  have ht' : MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D)
      (Mathieu12Points D) (Set.range e).ncard := hn.symm ▸ ht
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht'
  have he := (fixingSubgroup (Mathieu12DodecadModel D) (Set.range e)).card_mul_index
  rw [hi,hn,mathieu12_degree,mathieu12_order] at he
  norm_num [Nat.choose,Nat.factorial] at he
  omega

end Atlas.Codes
