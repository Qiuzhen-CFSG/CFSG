module

public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeLocalData
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeModel.Generators
public import Theory.Mathieu.M24.Properties.Order
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# An inverted Heisenberg Sylow three-subgroup in M₂₄

In the actual automorphism group of the Witt design, the two certified cubic
permutations generate exactly the 27 words `a^i b^j [a,b]^k`, with coordinates
modulo three. Right multiplication by either generator or its inverse stays
in this list. The images of points 0 and 1 distinguish its entries, giving
an exact count. Since the three-part of the established order of M₂₄ is 27,
this generated subgroup is Sylow. The certified ambient involution inverts
both generators, yielding the unconditional local configuration used for
central-cover arguments.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, E.4.3(2), printed pp.241–242, and I.1.1–I.1.4, printed pp.407–408.
This module constructs the local configuration, without any multiplier claim.
-/

namespace Sporadic.Mathieu.M24ValueBoundParabolics
open scoped commutatorElement
open ThreeModel

set_option maxRecDepth 100000

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private abbrev Coordinates := Fin 3 × Fin 3 × Fin 3

private def normalPerm (u : Coordinates) : Equiv.Perm (Fin 24) :=
  aPerm ^ u.1.val * bPerm ^ u.2.1.val * ⁅aPerm, bPerm⁆ ^ u.2.2.val

private theorem normalPerm_mul_a : ∀ u : Coordinates,
    normalPerm u * aPerm = normalPerm (u.1 + 1, u.2.1, u.2.2 - u.2.1) := by
  decide +kernel

private theorem normalPerm_mul_b : ∀ u : Coordinates,
    normalPerm u * bPerm = normalPerm (u.1, u.2.1 + 1, u.2.2) := by
  decide +kernel

private theorem normalPerm_mul_a_inv : ∀ u : Coordinates,
    normalPerm u * aPerm⁻¹ = normalPerm (u.1 - 1, u.2.1, u.2.2 + u.2.1) := by
  decide +kernel

private theorem normalPerm_mul_b_inv : ∀ u : Coordinates,
    normalPerm u * bPerm⁻¹ = normalPerm (u.1, u.2.1 - 1, u.2.2) := by
  decide +kernel

private theorem normalPerm_distinguish : ∀ u v : Coordinates,
    normalPerm u 0 = normalPerm v 0 → normalPerm u 1 = normalPerm v 1 → u = v := by
  decide +kernel

private noncomputable def normalForm (u : Coordinates) : M24 :=
  a ^ u.1.val * b ^ u.2.1.val * ⁅a, b⁆ ^ u.2.2.val

private theorem normalForm_one : normalForm (0, 0, 0) = 1 := by
  simp [normalForm]

private theorem normalForm_mul_a (u : Coordinates) :
    normalForm u * a = normalForm (u.1 + 1, u.2.1, u.2.2 - u.2.1) := by
  exact Subtype.ext (normalPerm_mul_a u)

private theorem normalForm_mul_b (u : Coordinates) :
    normalForm u * b = normalForm (u.1, u.2.1 + 1, u.2.2) := by
  exact Subtype.ext (normalPerm_mul_b u)

private theorem normalForm_mul_a_inv (u : Coordinates) :
    normalForm u * a⁻¹ = normalForm (u.1 - 1, u.2.1, u.2.2 + u.2.1) := by
  exact Subtype.ext (normalPerm_mul_a_inv u)

private theorem normalForm_mul_b_inv (u : Coordinates) :
    normalForm u * b⁻¹ = normalForm (u.1, u.2.1 - 1, u.2.2) := by
  exact Subtype.ext (normalPerm_mul_b_inv u)

private theorem normalForm_injective : Function.Injective normalForm := by
  intro u v h
  exact normalPerm_distinguish u v
    (congrArg (fun g : M24 => (g : Equiv.Perm (Fin 24)) 0) h)
    (congrArg (fun g : M24 => (g : Equiv.Perm (Fin 24)) 1) h)

private noncomputable def candidate : Subgroup M24 :=
  Subgroup.closure ({a, b} : Set M24)

private theorem normalForm_mem (u : Coordinates) : normalForm u ∈ candidate := by
  have ha : a ∈ candidate := Subgroup.subset_closure (by simp)
  have hb : b ∈ candidate := Subgroup.subset_closure (by simp)
  have hc : ⁅a, b⁆ ∈ candidate := by
    rw [commutatorElement_def]
    exact candidate.mul_mem (candidate.mul_mem (candidate.mul_mem ha hb)
      (candidate.inv_mem ha)) (candidate.inv_mem hb)
  exact candidate.mul_mem (candidate.mul_mem (candidate.pow_mem ha _)
    (candidate.pow_mem hb _)) (candidate.pow_mem hc _)

private theorem exists_normalForm {g : M24} (hg : g ∈ candidate) :
    ∃ u, normalForm u = g := by
  apply Subgroup.closure_induction_right
    (p := fun x _ => ∃ u, normalForm u = x) ?_ ?_ ?_ hg
  · exact ⟨(0, 0, 0), normalForm_one⟩
  · intro x hx y hy ih
    obtain ⟨u, rfl⟩ := ih
    rcases hy with rfl | rfl
    · exact ⟨_, (normalForm_mul_a u).symm⟩
    · exact ⟨_, (normalForm_mul_b u).symm⟩
  · intro x hx y hy ih
    obtain ⟨u, rfl⟩ := ih
    rcases hy with rfl | rfl
    · exact ⟨_, (normalForm_mul_a_inv u).symm⟩
    · exact ⟨_, (normalForm_mul_b_inv u).symm⟩

private noncomputable def normalElement (u : Coordinates) : candidate :=
  ⟨normalForm u, normalForm_mem u⟩

private theorem candidate_card : Nat.card candidate = 27 := by
  have hbij : Function.Bijective normalElement := by
    constructor
    · intro u v h
      exact normalForm_injective (congrArg Subtype.val h)
    · intro g
      obtain ⟨u, hu⟩ := exists_normalForm g.property
      exact ⟨u, Subtype.ext hu⟩
  rw [← Nat.card_eq_of_bijective normalElement hbij]
  simp [Coordinates]

private theorem candidate_isPGroup : IsPGroup 3 candidate := by
  apply IsPGroup.of_card (n := 3)
  exact candidate_card

private theorem candidate_index : ¬ 3 ∣ candidate.index := by
  have h := candidate.card_mul_index
  rw [candidate_card, m24_order] at h
  have hi : candidate.index = 9067520 := by omega
  rw [hi]
  decide +kernel

/-- An actual Sylow three-subgroup of the Witt-design Mathieu group, with
Heisenberg generators simultaneously inverted by an ambient involution. -/
public noncomputable def invertedHeisenbergSylowThree :
    PerfectCentralCovering.InvertedHeisenbergSylowThree M24 where
  sylow := candidate_isPGroup.toSylow candidate_index
  a := a
  b := b
  inverter := t
  generate := rfl
  a_cube := a_cube
  b_cube := b_cube
  commutator_a := commutator_a
  commutator_b := commutator_b
  commutator_ne_one := commutator_ne_one
  inverter_sq := t_sq
  conjugate_a := conjugate_a
  conjugate_b := conjugate_b

end Sporadic.Mathieu.M24ValueBoundParabolics
