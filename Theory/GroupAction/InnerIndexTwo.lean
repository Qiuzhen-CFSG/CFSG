module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Index
/-! # An outer actor exhausts an index-two automorphism extension
If the actual outer automorphism group has order two, an action containing
all inner automorphisms and one outer automorphism is surjective. The proof
uses multiplication of subgroup indices and retains the given action.
-/
public section
open Subgroup
namespace MulAut
variable {A B:Type*} [Group A] [Group B]
theorem surjective_of_inner_le_of_outer_card_two
    (f:A→*MulAut B) (hi:innerSubgroup B≤f.range)
    (ho:Nat.card (Outer B)=2) (a:A) (ha:f a∉innerSubgroup B) :
    Function.Surjective f := by
  have hm:=relIndex_mul_index hi
  change (innerSubgroup B).index=2 at ho
  rw [ho] at hm
  have hp:((innerSubgroup B).relIndex f.range*f.range.index).Prime:=hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hR⟩|⟨_,hI⟩
  · exact f.range_eq_top.mp (index_eq_one.mp hR)
  · exact (ha (relIndex_eq_one.mp hI ⟨a,rfl⟩)).elim
end MulAut
