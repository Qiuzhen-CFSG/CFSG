module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Simple subgroups of small index

If a simple subgroup is larger than the factorial of its index, its action
on the ambient cosets is trivial. It therefore equals its normal core.
Groups of order at most six are solvable: except for order four their
orders are squarefree, and order four is abelian.

These two elementary facts give a solvable outer quotient for the canonical
PSL₃(4) subgroup of the incidence collineation group once the frame bound
puts its index at most six. The concrete consumer is
`Theory/SpecificGroups/PSL3Four/Collineations/PerfectImage.lean`.
-/

namespace Subgroup
variable {H : Type*} [Group H] [Finite H]
public theorem normal_of_simple_of_factorial_index_lt_card (N : Subgroup H)
    [IsSimpleGroup N] (hb : N.index.factorial < Nat.card N) : N.Normal := by
  let f : N →* Equiv.Perm (H ⧸ N) := (MulAction.toPermHom H (H ⧸ N)).comp N.subtype
  have ht : f.ker = ⊤ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hc := Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp h)
      rw [Nat.card_perm, ← N.index_eq_card] at hc
      omega
    · exact h
  have he : N.normalCore = N := by
    apply le_antisymm N.normalCore_le
    intro g hg
    rw [normalCore_eq_ker]
    exact (show (⟨g,hg⟩ : N) ∈ f.ker from ht ▸ mem_top _)
  rw [← he]
  infer_instance
end Subgroup

namespace Group
variable {H : Type*} [Group H] [Finite H]
public theorem isSolvable_of_card_le_six (hc : Nat.card H ≤ 6) : IsSolvable H := by
  by_cases h4 : Nat.card H = 4
  · let : Fact (Nat.Prime 2) := ⟨by decide⟩
    let : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by simpa using h4)
    exact isSolvable_of_comm (fun a b : H => IsMulCommutative.is_comm.comm a b)
  · have hp := Nat.card_pos (α := H)
    have hs : Squarefree (Nat.card H) := by
      interval_cases h : Nat.card H <;> norm_num [h] at *
      · exact Nat.prime_two.squarefree
      · exact Nat.prime_three.squarefree
      · exact (show Nat.Prime 5 by decide).squarefree
      · exact (Nat.squarefree_mul (show Nat.Coprime 2 3 by decide)).mpr
          ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
    let : IsZGroup H := IsZGroup.of_squarefree hs
    infer_instance
end Group
