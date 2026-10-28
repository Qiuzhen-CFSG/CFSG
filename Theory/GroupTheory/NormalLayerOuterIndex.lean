module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Index

/-!
# Index of a normal layer with its full centralizer retained

Conjugation has outer kernel K C_G(K). The relative index over K divides
|C_G(K)|, and the remaining quotient embeds in Out(K). Consequently the
index of K divides their product, without a centerless-layer assumption.
Source application: Aschbacher--Smith 11.2.1, printed pp.766--767.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A normal layer index divides the centralizer order times the outer order. -/
theorem normal_index_dvd_centralizer_mul_outer (K : Subgroup G) [K.Normal] :
    K.index ∣ Nat.card (centralizer (K : Set G)) * Nat.card (MulAut.Outer K) := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
    (MulAut.conjNormal : G →* MulAut K)
  have hk : f.ker = K ⊔ centralizer (K : Set G) := by
    ext x
    change QuotientGroup.mk' (MulAut.innerSubgroup K) (MulAut.conjNormal x) = 1 ↔ _
    rw [show QuotientGroup.mk' (MulAut.innerSubgroup K) (MulAut.conjNormal x) = 1 ↔
      MulAut.conjNormal x ∈ MulAut.innerSubgroup K from QuotientGroup.eq_one_iff _]
    change x ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal ↔ _
    rw [MulAut.conjNormal_comap_innerSubgroup]
  rw [← K.relIndex_mul_index (show K ≤ K ⊔ centralizer (K : Set G) from le_sup_left)]
  apply Nat.mul_dvd_mul
  · rw [relIndex_sup_left]
    exact K.relIndex_dvd_card _
  · rw [← hk, index_ker]
    exact f.range.card_subgroup_dvd_card

end Theory.GroupTheory
