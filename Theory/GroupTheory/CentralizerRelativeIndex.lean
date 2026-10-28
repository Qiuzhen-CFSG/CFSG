module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Centralizer orders from relative index

The centralizer of x inside a subgroup M is the literal intersection of M
with its ambient centralizer. If the relative index of that intersection
is prime to p, both centralizer orders have the same p-valuation. No normality
of M, and no containment of the full ambient centralizer in M, is needed.

This elementary order calculation is used in the centralizer comparison in
Aschbacher–Smith F.4.37–40, printed pp.293–294.
-/

public section
open Subgroup
namespace Theory.GroupTheory.CentralizerRelativeIndex
variable {G : Type*} [Group G]

/-- The literal local centralizer identifies with the ambient intersection. -/
def localCentralizerEquiv (M : Subgroup G) (x : M) :
    centralizer ({x} : Set M) ≃* (M ⊓ centralizer ({x.val} : Set G) : Subgroup G) where
  toFun u := ⟨u.val.val, u.val.property, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp u.property))⟩
  invFun u := ⟨⟨u.val,u.property.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp u.property.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Prime-to-p relative index preserves the p-valuation of the centralizer order. -/
theorem factorization_eq_of_not_dvd_relIndex [Finite G] (M : Subgroup G) (x : M) (p : ℕ)
    (ho : ¬ p ∣ (M ⊓ centralizer ({x.val} : Set G)).relIndex
      (centralizer ({x.val} : Set G))) :
    (Nat.card (centralizer ({x.val} : Set G))).factorization p =
      (Nat.card (centralizer ({x} : Set M))).factorization p := by
  let C := centralizer ({x.val} : Set G)
  let B := (M ⊓ C).subgroupOf C
  have hc : Nat.card B = Nat.card (centralizer ({x} : Set M)) :=
    (Nat.card_congr (subgroupOfEquivOfLe (show M ⊓ C ≤ C from inf_le_right)).toEquiv).trans
      (Nat.card_congr (localCentralizerEquiv M x).toEquiv).symm
  have hi : B.index ≠ 0 := B.index_ne_zero_of_finite
  have hz : B.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd ho
  have he := congrArg (fun k : ℕ => k.factorization p) B.card_mul_index
  rw [Nat.factorization_mul (Nat.card_pos.ne') hi,Finsupp.add_apply,hz,add_zero,hc] at he
  exact he.symm

end Theory.GroupTheory.CentralizerRelativeIndex
