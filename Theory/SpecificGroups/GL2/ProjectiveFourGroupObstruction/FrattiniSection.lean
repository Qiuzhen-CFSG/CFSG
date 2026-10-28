module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.LinearAction
public import Theory.GroupTheory.CharacteristicFrattiniAction

/-!
# Four-group obstruction from a characteristic Frattini plane

Let N be characteristic in H and suppose N/Φ(N) is an elementary abelian
odd plane. If the kernel of the inner action on that plane lies in a
characteristic subgroup W, no four-group of automorphisms of H acts
faithfully on H/W. Naturality sends scalar restrictions to automorphisms
trivial on H/W; a faithful four-group on an odd plane contains inversion.

This form retains arbitrary characteristic sections and does not require
N itself to be elementary abelian or self-centralizing. It supplies the
two terminal automorphism contradictions in Aschbacher--Smith §13.1,
printed p.876, including the non-elementary nilpotent radical case.
-/

public section
open Subgroup
namespace Subgroup
variable {H : Type*} [Group H]

/-- An automorphism centralizing the inner action on a characteristic
Frattini section is trivial modulo every characteristic overgroup of its
inner-action kernel. -/
theorem quotientAut_eq_one_of_frattiniAction_centralizes
    (N W : Subgroup H) [N.Characteristic] [W.Characteristic]
    (hk : (frattiniConjugation N).ker ≤ W) (a : MulAut H)
    (ha : characteristicFrattiniAction N a ∈
      centralizer ((frattiniConjugation N).range : Set _)) :
    quotientAut W a = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W x
  rw [quotientAut_apply_mk]
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  apply hk
  apply MonoidHom.mem_ker.mpr
  have hc := mem_centralizer_iff.mp ha (frattiniConjugation N x) ⟨x,rfl⟩
  have he := congrArg (quotientAut (frattini N))
    (characteristic_conjNormal_equivariant N a x)
  simp only [map_mul, map_inv] at he
  change characteristicFrattiniAction N a * frattiniConjugation N x *
    (characteristicFrattiniAction N a)⁻¹ = frattiniConjugation N (a x) at he
  rw [← hc, mul_inv_cancel_right] at he
  rw [map_mul, map_inv, ← he, inv_mul_cancel]

/-- A characteristic odd Frattini plane forbids faithful four-group
actions on the quotient detected by its inner action. -/
theorem four_group_quotient_action_not_injective_of_frattini_plane
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (N W : Subgroup H) [N.Characteristic] [W.Characteristic]
    [Finite (N ⧸ frattini N)] [IsElementaryAbelian p (N ⧸ frattini N)]
    (hN : Nat.card (N ⧸ frattini N) = p ^ 2)
    (hk : (frattiniConjugation N).ker ≤ W) (ρ : E →* MulAut H) :
    ¬ Function.Injective ((quotientAut W).comp ρ) := by
  let : Finite E := Nat.finite_of_card_ne_zero (by omega)
  intro hi
  let r := (characteristicFrattiniAction N).comp ρ
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply r.ker.eq_bot_iff_forall.mpr
    intro a ha
    apply hi
    rw [map_one]
    apply quotientAut_eq_one_of_frattiniAction_centralizes N W hk (ρ a)
    change r a ∈ centralizer ((frattiniConjugation N).range : Set _)
    rw [MonoidHom.mem_ker.mp ha]
    exact (centralizer _).one_mem
  obtain ⟨a, ha, hinv⟩ := IsElementaryAbelian.exists_inverting_of_four_group
    hp hN hE r hr
  apply ha
  apply hi
  rw [map_one]
  apply quotientAut_eq_one_of_frattiniAction_centralizes N W hk (ρ a)
  apply mem_centralizer_iff.mpr
  intro b _
  apply MulEquiv.ext
  intro v
  change b (r a v) = r a (b v)
  rw [hinv, hinv, map_inv]

end Subgroup
