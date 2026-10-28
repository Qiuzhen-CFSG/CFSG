module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Translation of an odd finite subset

An involution in a commutative group cannot preserve a finite subset of
odd cardinality unless it is the identity. Multiplying all members of the
subset proves the assertion without choosing pairs.

Source application: Aschbacher--Smith F.5.4(3), printed p.301.
-/

public noncomputable section
open scoped BigOperators

namespace Subgroup

theorem eq_one_of_involution_preserves_odd_subset {V : Type*} [CommGroup V]
    (S : Set V) [Finite S] (f : V) (hf : f ^ 2 = 1)
    (hodd : Odd (Nat.card S)) (hS : ∀ x ∈ S, f * x ∈ S) : f = 1 := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let e : Equiv.Perm S := {
    toFun x := ⟨f * x.val,hS x.val x.property⟩
    invFun x := ⟨f * x.val,hS x.val x.property⟩
    left_inv x := by apply Subtype.ext; change f * (f * x.val) = x.val; rw [←mul_assoc,←pow_two,hf,one_mul]
    right_inv x := by apply Subtype.ext; change f * (f * x.val) = x.val; rw [←mul_assoc,←pow_two,hf,one_mul] }
  have he : (∏ x : S, f * x.val) = ∏ x : S, x.val :=
    Fintype.prod_equiv e (fun x => f * x.val) (fun x => x.val) (fun _ => rfl)
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at he
  have hp : f ^ Fintype.card S = 1 := mul_right_cancel (he.trans (one_mul _).symm)
  rw [←Nat.card_eq_fintype_card] at hp
  obtain ⟨n,hn⟩ := hodd
  rw [hn,pow_add,pow_mul,hf,one_pow,one_mul,pow_one] at hp
  exact hp

end Subgroup
