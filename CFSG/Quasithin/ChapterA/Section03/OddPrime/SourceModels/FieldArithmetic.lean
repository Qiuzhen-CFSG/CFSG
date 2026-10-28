module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.Carriers
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualParameters
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# The field parameters of the circle construction

On a field of order 2^(6n), Frobenius has order 6n and its 2n-th power
has order three. This actor lies in an actual field Sylow three-subgroup,
whose order is the three-part of 6n. The graph--field actor used to define
the unitary circle group has square one.

These checks include n = 1 and correct the printed n₃ in A.3.16 without
adding a divisibility hypothesis on n.

Source: Aschbacher--Smith, Notation A.3.16, printed p.51; finite-field
Frobenius order. The prime-field algebra comparison follows the proof in
`Theory.SpecificGroups.PSL2.OuterInvolutionFormula`.
-/

@[expose] public section
noncomputable section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem frobenius_order {r : ℕ} (hc : Nat.card F = 2 ^ r) :
    orderOf (frobeniusEquiv F 2) = r := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let f : (F ≃ₐ[ZMod 2] F) →* (F ≃+* F) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun _ _ h => AlgEquiv.ext fun x =>
    DFunLike.congr_fun h x
  have he : f (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) =
      frobeniusEquiv F 2 := by
    ext x
    change x ^ Fintype.card (ZMod 2) = x ^ 2
    rw [ZMod.card]
  rw [← he, orderOf_injective f hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm.trans hc

/-- The corrected field actor has order three for every positive n. -/
theorem circleField_order {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ (6 * n)) :
    orderOf (circleField F n) = 3 := by
  have ho := frobenius_order hc
  have hh := orderOf_pow_orderOf_div (x := frobeniusEquiv F 2)
    (ho.symm ▸ (by omega : 6 * n ≠ 0))
    (ho.symm ▸ (by omega : 3 ∣ 6 * n))
  simpa only [circleField, ho, show 6 * n / 3 = 2 * n by omega] using hh

/-- The induced field automorphism of the actual PSL₃ carrier also has order three. -/
theorem circleField_actor_order {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) :
    orderOf (fieldAction F (circleField F n)) = 3 := by
  rw [orderOf_injective (fieldAction F)
    Matrix.PSL3.CartanActions.ResidualParameters.fieldAction_injective]
  exact circleField_order hn hc

omit [CharP F 2] in
/-- The actual field Sylow three-subgroups have order (6n)₃, not n₃. -/
theorem fieldSylow_card {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n))
    (P : Sylow 3 (F ≃+* F)) :
    Nat.card P = 3 ^ (6 * n).factorization 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  rw [P.card_eq_multiplicity,
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hc]

/-- The chosen order-three actor belongs to a genuine field Sylow subgroup. -/
theorem circleField_le_sylow {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) :
    ∃ P : Sylow 3 (F ≃+* F), zpowers (circleField F n) ≤ P := by
  apply IsPGroup.exists_le_sylow
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, circleField_order hn hc, pow_one]

/-- The source graph--field map is involutory on the actual projective group. -/
theorem circleGraphField_sq {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    circleGraphField F n ^ 2 = 1 := by
  have hpow : ((frobeniusEquiv F 2) ^ (3 * n)) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * n * 2 = 6 * n by omega, ← frobenius_order hc]
    exact pow_orderOf_eq_one _
  rw [circleGraphField, (field_commute_graph _).symm.mul_pow,
    graph_sq, ← map_pow, hpow, map_one, one_mul]

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
