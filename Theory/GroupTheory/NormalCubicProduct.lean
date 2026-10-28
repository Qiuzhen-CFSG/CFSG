module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup

/-!
# The quotient by a commuting normal cubic product

The simultaneous action on Out(K) and Aut(X) has kernel KX when K commutes
with the abelian X and C_H(K) ∩ C_H(X) ≤ X. For |X| = 3, Aut(X) has order two.
Consequently H/KX is a two-group whenever Out(K) is a two-group.

This is the structural quotient calculation preceding the Clifford argument
in Aschbacher–Smith 13.8.21(1), printed p.956. It uses no splitting of H.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.NormalCubicProduct
variable {H : Type*} [Group H]
variable (K X : Subgroup H) [K.Normal] [X.Normal]
/-- The simultaneous outer action on K and conjugation action on X. -/
def jointOuterAction : H →* MulAut.Outer K × MulAut X :=
  ((QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
    (MulAut.conjNormal : H →* MulAut K)).prod MulAut.conjNormal

/-- The joint-centralizer bound identifies the actual kernel with KX. -/
theorem jointOuterAction_ker [IsMulCommutative X]
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hjoint : centralizer (K : Set H) ⊓ centralizer (X : Set H) ≤ X) :
    (jointOuterAction K X).ker = K ⊔ X := by
  have hK : K ≤ centralizer (X : Set H) := by
    intro k hk x hx
    exact (hc ⟨k, hk⟩ ⟨x, hx⟩).eq.symm
  have hX : X ≤ centralizer (K : Set H) := by
    intro x hx k hk
    exact (hc ⟨k, hk⟩ ⟨x, hx⟩).eq
  rw [jointOuterAction, MonoidHom.ker_prod, ← MonoidHom.comap_ker,
    QuotientGroup.ker_mk', MulAut.conjNormal_comap_innerSubgroup,
    MulAut.conjNormal_ker_eq_centralizer]
  apply le_antisymm
  · intro a ha
    obtain ⟨k, hk, c, hcK, rfl⟩ := mem_sup_of_normal_right.mp ha.1
    have hcX : c ∈ centralizer (X : Set H) :=
      (mul_mem_cancel_left (hK hk)).mp ha.2
    exact (K ⊔ X).mul_mem ((show K ≤ K ⊔ X from le_sup_left) hk)
      ((show X ≤ K ⊔ X from le_sup_right) (hjoint ⟨hcK, hcX⟩))
  · apply sup_le
    · exact le_inf le_sup_left hK
    · exact le_inf (hX.trans le_sup_right) (le_centralizer X)

/-- For a normal cubic factor, a two-group outer action makes H/KX a two-group. -/
theorem quotient_isTwoGroup [Finite H]
    (hcard : Nat.card X = 3)
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hjoint : centralizer (K : Set H) ⊓ centralizer (X : Set H) ≤ X)
    (houter : IsPGroup 2 (MulAut.Outer K)) : IsPGroup 2 (H ⧸ (K ⊔ X)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsCyclic X := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut X) = 2 := by
    rw [IsCyclic.card_mulAut, hcard]
    decide
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp houter
  have hp : IsPGroup 2 (MulAut.Outer K × MulAut X) :=
    IsPGroup.of_card (n := n + 1) (by rw [Nat.card_prod, hn, hAut, pow_succ])
  let e : (H ⧸ (K ⊔ X)) ≃* (jointOuterAction K X).range :=
    (QuotientGroup.quotientMulEquivOfEq (jointOuterAction_ker K X hc hjoint).symm).trans
      (QuotientGroup.quotientKerEquivRange (jointOuterAction K X))
  exact (hp.to_subgroup _).of_equiv e.symm
end Theory.GroupTheory.NormalCubicProduct
