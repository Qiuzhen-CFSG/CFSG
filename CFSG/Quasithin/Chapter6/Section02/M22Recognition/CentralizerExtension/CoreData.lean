module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.Data.Fintype.Perm

/-!+# The extraspecial data preceding the centralizer construction

These are the intrinsic inputs on printed p.688 (PDF p.705) of
Aschbacher–Smith, Proposition 6.2.13, in the branch `C_R(K) = Z`. The group
parameter is the actual involution centralizer `H`, and `P` is its normal
extraspecial subgroup `O₂(K)`. Plus type is expressed by actual commuting
quaternion factors, using the existing central-product interface. The quotient
is the actual quotient by `P`; the Sylow-three centralizer is computed in `H`.

The elementary-eight geometry is not part of this input, nor is any elementary
sixteen, symmetric-four quotient, splitting, or global recognition conclusion.
The natural `L₂(4)` extension and the marked conjugator live in the surrounding
ambient group and must be retained by the later source adapter. `CoreData` does
not replace those compatible ambient inputs.

The elementary consequences here are the order of `H` and centrality in `H`
of the actual center of `P`. Centrality follows because this is a normal
subgroup of order two.
-/

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension

open Subgroup

/-- Intrinsic earlier inputs, with all normality relative to `H`. -/
public structure CoreData {H : Type*} [Group H] (P : Subgroup H) [P.Normal] : Prop where
  plusType : Nonempty (QuaternionCentralProductData P)
  quotient : Nonempty ((H ⧸ P) ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
  selfCentralizing : centralizer (P : Set H) ≤ P
  sylowThreeCentralizer : ∃ X : Sylow 3 H,
    P ⊓ centralizer (X : Set H) = (center P).map P.subtype

variable {H : Type*} [Group H] [Finite H] {P : Subgroup H} [P.Normal]

/-- The order follows from the extraspecial core and the genuine quotient. -/
public theorem CoreData.card (h : CoreData P) : Nat.card H = 384 := by
  obtain ⟨d⟩ := h.plusType
  obtain ⟨e⟩ := h.quotient
  have hQ : Nat.card (H ⧸ P) = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      change Nat.card (ZMod 2) = 2
      exact Nat.card_zmod 2
    rw [h3, h2]
  rw [card_eq_card_quotient_mul_card_subgroup P, hQ, d.card]

/-- The core's center is central in the overgroup, using its order two. -/
public theorem CoreData.center_le (h : CoreData P) :
    (center P).map P.subtype ≤ center H := by
  let : ((center P).map P.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  apply central_of_normal_card_two
  rw [card_map_of_injective P.subtype_injective]
  obtain ⟨d⟩ := h.plusType
  exact d.center_card

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
