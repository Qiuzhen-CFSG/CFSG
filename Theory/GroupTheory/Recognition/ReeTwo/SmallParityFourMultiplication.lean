module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates
public import Theory.SpecificGroups.ReeTwo.ZeroHeadAction

/-!
# Subgroup laws and multiplicativity for the rank-four parity carriers

The eight fixed carrier predicates define subgroups of the verified Sylow
model. Multiplication follows from the polynomial complement action on the
core with `b₀ = b₁ = 0`; inverse closure follows from finite order. The same
formulas prove that the four prescribed coordinates are multiplicative.
For row 7, the carrier equation eliminates `b₆`, and the binary identity
`u² = u` verifies the quadratic correction `b₇ + b₆ t₁`.

No identification with a generator closure or Frattini subgroup is used here.
Source: Shinoda (1975), (2.3), pp. 81–82, through `Core`, `RootAction`,
`Sylow`, and `ZeroHeadAction`; the row conventions are those of
`SmallParityFourCoordinates`.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem low_mul (t s : FiveFour.Cyclic 4) :
    (((t * s).toAdd.val : ℕ) : ZMod 2) = (t.toAdd.val : ZMod 2) + (s.toAdd.val : ZMod 2) :=
  (by decide : ∀ t s : FiveFour.Cyclic 4,
    (((t * s).toAdd.val : ℕ) : ZMod 2) = (t.toAdd.val : ZMod 2) + (s.toAdd.val : ZMod 2)) t s

private theorem high_mul (t s : FiveFour.Cyclic 4) :
    (((t * s).toAdd.val / 2 : ℕ) : ZMod 2) = (t.toAdd.val / 2 : ℕ) +
      (s.toAdd.val / 2 : ℕ) + (t.toAdd.val : ZMod 2) * (s.toAdd.val : ZMod 2) :=
  (by decide : ∀ t s : FiveFour.Cyclic 4,
    (((t * s).toAdd.val / 2 : ℕ) : ZMod 2) = (t.toAdd.val / 2 : ℕ) +
      (s.toAdd.val / 2 : ℕ) + (t.toAdd.val : ZMod 2) * (s.toAdd.val : ZMod 2)) t s

private theorem carrier_mul (i : Fin 8) (x y : SylowModel)
    (hx : smallParityFourCarrier i x) (hy : smallParityFourCarrier i y) :
    smallParityFourCarrier i (x * y) := by
  have hm : (x * y).left = Core.mul x.left (Core.zeroHeadAction x.right y.left) := by
    rw [SemidirectProduct.mul_left, MonoidHom.comp_apply,
      Core.complementAction_of_zero_head _ _ hy.1 hy.2.1]
    rfl
  simp only [smallParityFourCarrier, hm, SemidirectProduct.mul_right, low_mul, high_mul] at *
  fin_cases i <;> simp_all [Core.zeroHeadAction, Core.mul]
  have hx6 := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c) _ _ _ hx.2.2.2.2
  have hy6 := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c) _ _ _ hy.2.2.2.2
  simp only [hx.2.2.2.1] at hx6
  simp only [hy.2.2.2.1] at hy6
  rw [hx6, hy6]
  ring_nf
  reduce_mod_char

/-- The fixed quotient coordinates preserve multiplication on their specified carriers. -/
public theorem smallParityFourCoordinates_mul_of_carrier (i : Fin 8) (x y : SylowModel)
    (hx : smallParityFourCarrier i x) (hy : smallParityFourCarrier i y) :
    smallParityFourCoordinates i (x * y) =
      smallParityFourCoordinates i x * smallParityFourCoordinates i y := by
  have hm : (x * y).left = Core.mul x.left (Core.zeroHeadAction x.right y.left) := by
    rw [SemidirectProduct.mul_left, MonoidHom.comp_apply,
      Core.complementAction_of_zero_head _ _ hy.1 hy.2.1]
    rfl
  apply Multiplicative.toAdd.injective
  funext j
  simp only [smallParityFourCoordinates, hm, SemidirectProduct.mul_right, low_mul, high_mul]
  fin_cases i <;> fin_cases j <;>
    simp_all [smallParityFourCarrier, Core.zeroHeadAction, Core.mul]
  all_goals ring_nf
  all_goals reduce_mod_char
  have hx6 := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c) _ _ _ hx.2.2.2.2
  have hy6 := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c) _ _ _ hy.2.2.2.2
  simp only [hx.2.2.2.1] at hx6
  simp only [hy.2.2.2.1] at hy6
  rw [hx6, hy6]
  ring_nf
  reduce_mod_char
  simp only [(by decide : ∀ a : ZMod 2, a ^ 2 = a)]
  ring_nf
  reduce_mod_char

private theorem carrier_one (i : Fin 8) : smallParityFourCarrier i 1 := by
  fin_cases i <;> simp [smallParityFourCarrier] <;> decide

/-- The fixed carrier equations define a subgroup, independently of generator closure. -/
@[expose] public def smallParityFourCarrierSubgroup (i : Fin 8) : Subgroup SylowModel where
  carrier := {x | smallParityFourCarrier i x}
  one_mem' := by exact carrier_one i
  mul_mem' := by exact carrier_mul i _ _
  inv_mem' {a} ha := by
    have hp (n : ℕ) : smallParityFourCarrier i (a ^ n) := by
      induction n with
      | zero => simpa only [pow_zero] using carrier_one i
      | succ n ih => rw [pow_succ]; exact carrier_mul i _ _ ih ha
    rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a,
      ← pow_sub a (orderOf_pos a)]
    exact hp (orderOf a - 1)

/-- Membership is precisely the original carrier predicate, with all row equations unchanged. -/
@[simp] public theorem mem_smallParityFourCarrierSubgroup (i : Fin 8) (x : SylowModel) :
    x ∈ smallParityFourCarrierSubgroup i ↔ smallParityFourCarrier i x := Iff.rfl

end ReeTwo.SylowModel
