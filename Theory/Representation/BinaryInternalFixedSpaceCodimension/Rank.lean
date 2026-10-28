module

public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Binary codimension under an internal inclusion

For elementary abelian two-subgroups V ≤ W, the rank of V/(V ∩ C) is
at most the rank of W/(W ∩ C). Equality holds precisely when W = (W ∩ C)V.
We use the actual relative indices: the quotient-rank bridge identifies their
base-two logarithms, and the index formula for a subgroup chain detects when
the product fills W. All normality used here is inside the abelian group W.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the dimension step of B.2.18, printed p.81.
-/

open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryInternalFixedSpaceCodimension
variable {G : Type*} [Group G] [Finite G]

/-- The published difference of binary ranks is the logarithm of the relative index. -/
public theorem rank_eq_log_index (W C : Subgroup G) [IsElementaryAbelian 2 W] :
    Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ C)) =
      Nat.log 2 (C.relIndex W) := by
  rw [log_card_sub_log_card_eq_log_relIndex W (W ⊓ C) inf_le_left,
    inf_relIndex_left]

/-- Restricting the internal module cannot increase its quotient rank. -/
public theorem rank_mono (V W C : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V ≤ W) :
    Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card ↥(V ⊓ C)) ≤
      Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ C)) := by
  rw [rank_eq_log_index, rank_eq_log_index]
  exact Nat.log_mono_right (relIndex_le_of_le_right hVW (C.subgroupOf W).index_ne_zero_of_finite)

omit [Finite G] in
private theorem inf_relIndex_of_le (V W C : Subgroup G) (hVW : V ≤ W) :
    (W ⊓ C).relIndex V = C.relIndex V := by
  rw [← inf_relIndex_right (W ⊓ C) V, ← inf_relIndex_right C V]
  congr 1
  ext x
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hVW h.2, h.1⟩, h.2⟩⟩

omit [Finite G] in
private theorem fixedIndex_sup (V W C : Subgroup G)
    [IsElementaryAbelian 2 W] (hVW : V ≤ W) :
    (W ⊓ C).relIndex ((W ⊓ C) ⊔ V) = (W ⊓ C).relIndex V := by
  have h := relIndex_sup_left (V.subgroupOf W) ((W ⊓ C).subgroupOf W)
  rw [← subgroupOf_sup inf_le_left hVW,
    relIndex_subgroupOf (sup_le inf_le_left hVW), relIndex_subgroupOf hVW] at h
  exact h

/-- Equality of quotient ranks characterizes the internal supplement. -/
public theorem rank_eq_iff_supplement (V W C : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V ≤ W) :
    (Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card ↥(V ⊓ C)) =
      Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ C))) ↔
      W = (W ⊓ C) ⊔ V := by
  rw [rank_eq_log_index, rank_eq_log_index]
  have hidx := fixedIndex_sup V W C hVW
  have hinf := inf_relIndex_of_le V W C hVW
  constructor
  · intro hlog
    have heq : C.relIndex V = C.relIndex W := by
      rw [relIndex_eq_two_pow_quotient_finrank,
        relIndex_eq_two_pow_quotient_finrank]
      congr 1
      simpa only [log_relIndex_eq_quotient_finrank] using hlog
    have hmul := relIndex_mul_relIndex (W ⊓ C) ((W ⊓ C) ⊔ V) W
      le_sup_left (sup_le inf_le_left hVW)
    rw [hidx, hinf, inf_relIndex_left, heq] at hmul
    have hone : ((W ⊓ C) ⊔ V).relIndex W = 1 := by
      exact Nat.mul_left_cancel
        (Nat.pos_of_ne_zero (C.subgroupOf W).index_ne_zero_of_finite)
        (hmul.trans (Nat.mul_one _).symm)
    exact le_antisymm (relIndex_eq_one.mp hone) (sup_le inf_le_left hVW)
  · intro hsup
    rw [← hsup, inf_relIndex_left, hinf] at hidx
    exact congrArg (Nat.log 2) hidx.symm

end Representation.BinaryInternalFixedSpaceCodimension
