module
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Core collapse from a local actor supplement

Suppose X lies in AQ, Q commutes with R modulo V, and R normalizes VA.
Then [X,R] lies in VA. A subgroup generated modulo V by these commutators
and centralizing V lies in V whenever C_A(V) lies in V.

This is the elementary subgroup step in the central-cover argument of
Aschbacher–Smith 8.2.10(3), printed p.721. It retains the entire Q and X;
no splitting of a central extension is assumed.
-/

public section
open scoped IsMulCommutative commutatorElement Pointwise
namespace Subgroup
variable {G : Type*} [Group G]
/-- A core generated modulo V by local commutators lies in V when the local
actor is faithful modulo V and the supplement acts trivially modulo V. -/
theorem core_le_module_of_parabolic_commutator
    (V A Q X R K : Subgroup G) [IsMulCommutative V]
    (hAN : A ≤ normalizer (V : Set G))
    (hQN : Q ≤ normalizer ((V ⊔ A : Subgroup G) : Set G))
    (hRN : R ≤ normalizer ((V ⊔ A : Subgroup G) : Set G))
    (hX : X ≤ A ⊔ Q) (hQ : ⁅Q,R⁆ ≤ V)
    (hK : K ≤ ⁅X,R⁆ ⊔ V)
    (hKC : K ≤ centralizer (V : Set G))
    (hAC : A ⊓ centralizer (V : Set G) ≤ V) : K ≤ V := by
  let W := V ⊔ A
  have hAW : A ≤ W := le_sup_right
  have hcomm : ⁅X,R⁆ ≤ W := by
    have hp : A ⊔ Q ≤ commutatorPreimage (normalizer (W : Set G)) R W :=
      sup_le (le_commutatorPreimage (hAW.trans W.le_normalizer)
        ((commutator_mono hAW le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hRN)))
        (le_commutatorPreimage hQN (hQ.trans le_sup_left))
    exact (commutator_mono (hX.trans hp) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_rfl)
  have hKW : K ≤ W := hK.trans (sup_le hcomm le_sup_left)
  intro k hk
  have hm : k ∈ (V : Set G) * A := by
    rw [←coe_mul_of_right_le_normalizer_left V A hAN]
    exact hKW hk
  obtain ⟨v,hv,a,ha,rfl⟩ := hm
  have haC : a ∈ centralizer (V : Set G) :=
    (centralizer (V : Set G)).mul_mem_cancel_left (V.le_centralizer hv) |>.mp (hKC hk)
  exact V.mul_mem hv (hAC ⟨ha,haC⟩)
end Subgroup
