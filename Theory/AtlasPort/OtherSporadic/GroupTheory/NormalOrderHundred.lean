/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NormalOrderHundred.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSylowEight

/-!
# NormalOrderHundred

A faithful primitive action of degree one hundred has no normal subgroup of order one hundred.
Its unique Sylow five subgroup would be characteristic and transitive with only twenty-five elements.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NormalOrderHundred.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
local instance normalHundredPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The Sylow five subgroup of a group of order one hundred has order twenty-five. -/
theorem sylow_five_card_of_hundred {N : Type*} [Group N] [Finite N]
    (hn : Nat.card N = 100) (P : Sylow 5 N) : Nat.card P = 25 := by
  rw [Sylow.card_eq_multiplicity,hn]
  decide +kernel

/-- Divisibility by four and congruence to one modulo five force uniqueness. -/
theorem sylow_five_unique_of_hundred {N : Type*} [Group N] [Finite N]
    (hn : Nat.card N = 100) : Nat.card (Sylow 5 N) = 1 := by
  let P : Sylow 5 N := Classical.choice inferInstance
  have hp := sylow_five_card_of_hundred hn P
  have hi : P.index = 4 := by
    have he := P.toSubgroup.card_mul_index
    rw [hp,hn] at he
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hm : Nat.card (Sylow 5 N) % 5 = 1 := card_sylow_modEq_one 5 N
  omega

/-- A faithful primitive action of degree one hundred has no normal subgroup of order one hundred.
Its characteristic Sylow subgroup would have to be transitive while having only twenty-five elements. -/
theorem primitive_no_normal_order_hundred {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (x : X) (hx : Nat.card X = 100) (N : Subgroup G) [N.Normal]
    (hn : Nat.card N = 100) : False := by
  have hs := sylow_five_unique_of_hundred hn
  let : Subsingleton (Sylow 5 N) := (Nat.card_eq_one_iff_unique.mp hs).1
  let P : Sylow 5 N := Classical.choice inferInstance
  let Q := P.toSubgroup.map N.subtype
  let : Q.Normal := characteristic_in_normal N P.toSubgroup
  have hq : Nat.card Q = 25 := by
    rw [← Nat.card_congr (P.toSubgroup.equivMapOfInjective N.subtype Subtype.val_injective).toEquiv]
    exact sylow_five_card_of_hundred hn P
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hq
    omega
  let : IsPretransitive Q X := normal_pretransitive Q hne
  have hd := transitive_degree_dvd (G := Q) x
  rw [hx,hq] at hd
  norm_num at hd

end Atlas.GroupTheory
