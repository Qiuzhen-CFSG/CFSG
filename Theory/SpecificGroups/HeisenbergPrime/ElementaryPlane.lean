module

public import Theory.SpecificGroups.HeisenbergPrime

/-!
# An elementary plane in the prime Heisenberg group

The coordinate plane (a,0,c) is the image of the additive pair (a,c).
Its embedding proves its order is p²; the exponent-p identity makes it
an elementary abelian subgroup. This is the plane used when adjoining
an independent centralizing p-element in Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.1.33(2), printed p.29.
-/

open Subgroup

namespace HeisenbergPrime
variable {p : ℕ} [Fact p.Prime]

/-- Embed the additive coordinate plane into the Heisenberg group. -/
@[expose] public def planeEmbedding : Multiplicative (ZMod p × ZMod p) →* HeisenbergPrime p where
  toFun v := ⟨v.toAdd.1, 0, v.toAdd.2⟩
  map_one' := rfl
  map_mul' u v := by
    apply HeisenbergPrime.ext <;> simp [HeisenbergPrime.mul_a, HeisenbergPrime.mul_b,
      HeisenbergPrime.mul_c]

public theorem planeEmbedding_injective : Function.Injective (planeEmbedding (p := p)) := by
  intro u v h
  apply Multiplicative.toAdd.injective
  exact Prod.ext (congrArg HeisenbergPrime.a h) (congrArg HeisenbergPrime.c h)

/-- The concrete extraspecial group contains an elementary plane. -/
public theorem exists_elementary_plane (hp : p ≠ 2) :
    ∃ E : Subgroup (HeisenbergPrime p), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  let E := (planeEmbedding (p := p)).range
  have hc : Nat.card E = p ^ 2 := by
    rw [Nat.card_congr (MonoidHom.ofInjective planeEmbedding_injective).toEquiv.symm]
    change Nat.card (ZMod p × ZMod p) = p ^ 2
    rw [Nat.card_prod, Nat.card_zmod, pow_two]
  refine ⟨E, { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
               exponent_dvd_p := ?_ }, hc⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  exact Subtype.ext (pow_prime hp x)

end HeisenbergPrime

