module

public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Centralizer indices in the literal elementary quotient action

The quotient conjugation representation identifies fixed vectors with the
actual subgroup centralizer. Cardinality and rank-nullity therefore identify
its moving index with the binary fixed codimension. This bridge retains the
specified quotient map and works without finiteness of the ambient group.

Source application: MS93 (5.0), printed p.912, for the actual U-layer.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] [Finite V]
variable (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = centralizer (V : Set G))
theorem centralizer_index_eq_fixedCodim (A : Subgroup G) :
    (centralizer (A : Set G)).relIndex V =
      2 ^ fixedCodim (representation V q hq hker) (A.map q) := by
  let ρ := representation V q hq hker
  have hc : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) := by
    rw [←Nat.card_congr (fixedSpaceEquiv V q hq hker A)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := fixedSpace ρ (A.map q))
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    change Nat.card (Additive V) = _
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive V)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
    (V ⊓ centralizer (A : Set G)) V bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hc,hV,
    ←fixedCodim_add_finrank ρ (A.map q),pow_add] at hh
  exact Nat.eq_of_mul_eq_mul_left (n := 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.map q))) (by positivity)
    (by simpa only [mul_comm] using hh)
end Representation.NormalElementaryQuotient
