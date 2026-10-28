module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MonoidHom

/-! A finite simple source has no nontrivial homomorphism to a smaller finite group. -/

theorem eq_one_of_isSimpleGroup_of_card_lt
    {G K : Type*} [Group G] [Group K] [Finite G] [Finite K]
    [IsSimpleGroup G] (f : G →* K) (hcard : Nat.card K < Nat.card G) : f = 1 := by
  by_cases hker : f.ker = ⊥
  · have hinj : Function.Injective f := f.ker_eq_bot_iff.mp hker
    have hle : Nat.card G ≤ Nat.card K := Nat.card_le_card_of_injective f hinj
    exact False.elim ((Nat.not_le_of_lt hcard) hle)
  · have htop : f.ker = ⊤ := f.normal_ker.eq_bot_or_eq_top.resolve_left hker
    exact f.ker_eq_top_iff.mp htop

end MonoidHom
