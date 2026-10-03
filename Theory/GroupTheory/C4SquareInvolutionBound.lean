module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Square-one subgroups in C4 squared

In a finite group supplied with a C4×C4 model, any subgroup whose elements
all square to one has order at most four. Thus a subgroup of order greater
than four contains a primitive point, meaning a point with nontrivial square.

The supplied model injects the subgroup into the concrete square-one
subtype of C4×C4. Computing its four elements gives the bound; the second
statement is the contrapositive. This counting step supports the fixed-point
and coatom arguments of Stellmacher (10.1)(a3), printed pp.61–62 of
`refs/files/stellmacher-n-group.pdf`, without any ambient graph hypotheses.
-/

namespace Subgroup

public theorem card_le_four_of_c4_square_square_one
    {G : Type*} [Group G] [Finite G]
    (model : Nonempty (G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (K : Subgroup G) (hK : ∀ x ∈ K, x^2=1) : Nat.card K≤4 := by
  obtain ⟨e⟩ := model
  let f : K → {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1} :=
    fun x => ⟨e x,by rw [← map_pow,hK x x.property,e.map_one]⟩
  have hf : Function.Injective f := by
    intro x y heq
    exact Subtype.ext (e.injective (congrArg Subtype.val heq))
  have hcard : Nat.card {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1}=4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcard ▸ Nat.card_le_card_of_injective f hf

public theorem exists_square_ne_one_of_c4_square_card_gt_four
    {G : Type*} [Group G] [Finite G]
    (model : Nonempty (G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (K : Subgroup G) (hK : 4<Nat.card K) : ∃ x:G, x∈K ∧ x^2≠1 := by
  by_contra! hnone
  have hh := card_le_four_of_c4_square_square_one model K hnone
  omega

end Subgroup
