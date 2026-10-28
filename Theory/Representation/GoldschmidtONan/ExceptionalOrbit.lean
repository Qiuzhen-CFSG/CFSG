module

public import Theory.Representation.GoldschmidtONan.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The seven-point orbit in the exceptional Goldschmidt–O'Nan case

A faithful binary representation of dimension three is transitive on its
nonzero vectors whenever seven divides the group order. Cauchy's theorem
gives an element of order seven. Faithfulness preserves its order in the
permutation action on the seven nonzero vectors, so it is a single cycle.
No irreducibility, normal seven-subgroup, or model-recognition input is used.

This is the exceptional-case exclusion needed in Aschbacher–Smith,
Proposition 2.2.2, printed p.520.
-/

public section

namespace Representation.GoldschmidtONan

variable {X V : Type*} [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) X V}

theorem nonzeroTransitive_of_finrank_three_of_seven_dvd
    (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 3)
    (hseven : 7 ∣ Nat.card X) : NonzeroTransitive ρ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let A := {v : V // v ≠ 0}
  let : Fintype A := Fintype.ofFinite A
  have hcV : Fintype.card V = 8 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), hdim]
    norm_num
  have hcA : Fintype.card A = 7 := by
    change Fintype.card {v : V // v ≠ 0} = 7
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcV]
  let : MulAction X A := {
    smul x v := ⟨ρ x v, fun he => v.property
      (action_injective x (by simpa only [map_zero] using he))⟩
    one_smul v := Subtype.ext (by change ρ 1 (v : V) = v; simp)
    mul_smul x y v := Subtype.ext (by
      change ρ (x * y) (v : V) = ρ x (ρ y v)
      rw [map_mul, Module.End.mul_apply]) }
  let f : X →* Equiv.Perm A := MulAction.toPermHom X A
  have hf : Function.Injective f := by
    intro x y hxy
    apply hfaithful
    ext v
    by_cases hv : v = 0
    · simp [hv]
    · exact congrArg Subtype.val (congrArg (fun e : Equiv.Perm A => e ⟨v, hv⟩) hxy)
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  have ho : orderOf (f x) = Fintype.card A :=
    (orderOf_injective f hf x).trans (hx.trans hcA.symm)
  have hcycle : (f x).IsCycle := Equiv.Perm.isCycle_of_prime_order''
    (by rw [hcA]; decide) ho
  have hsupport : (f x).support = Finset.univ :=
    Finset.eq_univ_of_card _ (hcycle.orderOf.symm.trans ho)
  have hmoved (v : A) : f x v ≠ v :=
    Equiv.Perm.mem_support.mp (by rw [hsupport]; exact Finset.mem_univ v)
  intro v hv w hw
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq (hmoved ⟨v, hv⟩) (hmoved ⟨w, hw⟩)
  refine ⟨x ^ n, ?_⟩
  rw [← map_pow] at hn
  exact congrArg Subtype.val hn

/-- The literal exceptional GO alternative acts transitively on all seven
nonzero vectors of the given representation. -/
theorem Input.nonzeroTransitive_of_exceptional {Y : Subgroup X}
    (h : Input ρ Y) (he : ExceptionalCase ρ Y) : NonzeroTransitive ρ :=
  nonzeroTransitive_of_finrank_three_of_seven_dvd h.faithful he.2.1
    (by rw [he.2.2.1]; decide)

end Representation.GoldschmidtONan
